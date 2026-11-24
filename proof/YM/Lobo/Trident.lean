import YM.Lobo.Fox
import YM.Next.MAXWELL.Quarters
set_option maxHeartbeats 640000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
abbrev Tri:=Fin 3
abbrev edgeK(i:Tri):Tri:= i+1
abbrev backK(i:Tri):Tri:= i+2
abbrev lieu(i:Tri):Axis:=i.castSucc
abbrev Omega(i:Tri):= Ortho.plane (lieu (backK i)) (lieu (edgeK i))
-- cyclic exhaustive. k rotates from edge→back positive.
variable (k i j:Tri)(t:ℝ)
noncomputable def Thr (k:Tri)(t:ℝ):Ortho:=Ortho.oneParameter (Omega k) t
noncomputable def Cup(k:Tri):Signed:= Maxwell.Free.Corners.quarter (lieu (backK k)) (lieu (edgeK k))
noncomputable abbrev pathW(k:Tri): ℝ→ EuPin:= (MassiveTwoEstimates.SpinGeometry.geometry.path (Omega k)).choose
lemma treks (i:Tri): EuPin.Path (Omega i) (pathW i):= (MassiveTwoEstimates.SpinGeometry.geometry.path _).choose_spec
noncomputable def SpinQ (k:Tri):EuPin:= pathW k (Real.pi/2)
lemma fL(k:Tri): (SpinQ k).Lifts (Cup k):= ((treks k).2.2 _).trans (Maxwell.Free.Corners.sendsTime _ _ (show lieu (backK k) ≠ lieu (edgeK k) from (by fin_cases k <;> decide))).symm -- implicit h
set_option quotPrecheck false
local notation "K0"=> k
local notation "K1"=> edgeK k
local notation "K2"=> backK k
lemma threeL : K2≠ K1:=by fin_cases k <;> decide
lemma stateU: i=k∨i=K1∨i=K2:=by fin_cases k <;>fin_cases i<;> decide
-- ♎ helper identities create tactic. sequences along all.
lemma disjointI : k≠K1∧k≠K2∧K1≠K2:=by fin_cases k <;> decide
lemma tracesI : edgeK (edgeK k)= backK k∧ backK (edgeK k)=k ∧ edgeK (backK k)=k∧backK (backK k)=edgeK k:=by fin_cases k<;>decide
variable (a b:Axis)
local notation "C"=>Thr k t
local notation "x"=>lieu k
local notation "y"=>lieu (edgeK k)
local notation "z"=>lieu (backK k)
lemma stellar : (Thr k t).val a b= if a=z then Real.cos t * basis b z+ Real.sin t *basis b y else if a=y then Real.cos t*basis b y-Real.sin t*basis b z else basis b a:=by
     rw [← M4.move_basis (Thr k t).val a b]; have he:= Work.A13.plane_givens (show z ≠ y from fun h=>threeL k (Fin.castSucc_inj.1 h)) (basis b) t
     split <;> rename_i h; · rw[h]; exact he.1
     split <;> rename_i h'; · rw[h']; exact he.2.1
     exact he.2.2 a h h'
noncomputable def disk (k:Tri)(t:ℝ)(i j:Tri):ℂ:= ↑((Thr k t).val (lieu i) (lieu j))
variable (r:ℝ)
lemma outside(t:ℝ)(a: Axis): (Thr k t).val a timeAxis=if a=timeAxis then 1 else 0:=by
     rw [stellar]; fin_cases a<;>fin_cases k <;> simp +decide [basis_eq,lieu,timeAxis] -- loops
lemma indoor (t:ℝ) : (Thr k t).val timeAxis (lieu i)=0:=by rw [stellar]; fin_cases k<;>fin_cases i<;>simp +decide [basis_eq, timeAxis,lieu]
lemma triLast {M:Type}[AddCommMonoid M](f:Axis→ M) : ∑ i:Axis,f i=(∑ i:Tri,f (lieu i))+ f timeAxis:=Fin.sum_univ_castSucc f
-- roll coprojection. antisym takes special to vector
variable {M:Type}[AddCommGroup M][Module ℂ M]
noncomputable def palm (k:Tri)(t:ℝ)(f:Axis→M)(i:Axis):M:= ∑ a:Axis,(↑((Thr k t).val a i):ℂ) • f a
lemma lastB(f:Axis→M): palm k t f timeAxis=f timeAxis:=by
    unfold palm; simp_rw [outside]; rw [sum_eq_single timeAxis]; · simp
    · intro a _ h; simp[h]
    simp
noncomputable def wing(k:Tri)(t:ℝ)(f:Tri→M)(i:Tri):M:= ∑ j:Tri,disk k t j i • f j
lemma hat (f:Axis→M): palm k t f (lieu i)= wing k t (f ∘lieu) i:=by
    unfold palm; rw [triLast,indoor]; simp only [Complex.ofReal_zero, zero_smul,add_zero]; rfl
lemma wrapV(f:Axis→Axis→M):∑ i': Axis,∑ j':Axis,(↑((C).val i' a*(C).val j' b):ℂ) • f i' j'= palm k t (fun i'=> palm k t (f i') b) a:=by
    unfold palm; simp only[smul_sum, smul_smul,Complex.ofReal_mul]
lemma sumU(f:Tri→M) : ∑ i:Tri,f i=f k+f K1+f K2:=by
     rw [Fin.sum_univ_three]; fin_cases k; rfl;
     change _=f 1+f 2+f 0; abel;
     change _=f 2+f 0+f 1; abel
lemma wingsI(f:Tri→M):(wing k t f k=f k)∧ wing k t f (edgeK k) =(Real.cos t:ℂ) • f K1+(Real.sin t:ℂ) • f K2∧wing k t f (backK k)=(Real.cos t:ℂ) • f K2-(Real.sin t:ℂ) • f K1:=by
      simp_rw [wing, sumU k,disk,stellar]; fin_cases k<;> first|(simp +decide [basis_eq,lieu, Fin.ext_iff]; try module)|done
end YM.Lobo
#print axioms YM.Lobo.wingsI
#print axioms YM.Lobo.hat
#print axioms YM.Lobo.lastB
#print axioms YM.Lobo.fL
