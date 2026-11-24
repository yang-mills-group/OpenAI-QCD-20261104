import YM.Kwick.Libra
/-! Mixed triangular heights. Work w-hooks on *weighted columns*. Keep additive costs not multiplicative lower τ.P
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.Perla Tawny.Cast.TableT Tawny.Cast.Zinc
open Oriole Counting Counting.Click
local notation "Z"=> RawVec 10
variable (j:Axis)(x y:Z)(t:ℂ)(w:ℝ)
lemma wageS : wages j (t • x)= ‖t‖*wages j x:=by unfold wages; simp only[map_smul,norm_smul,mul_sum]
lemma wageA : wages j (x+y) ≤ wages j x+wages j y:=by unfold wages; rw [← Finset.sum_add_distrib]; apply sum_le_sum; intro i _; rw[map_add]; exact norm_add_le ..
lemma wageN : wages j (-x)=wages j x:=by unfold wages; simp_rw [map_neg,norm_neg]
lemma wageT : wages j (0:Z)=0:=by unfold wages; simp
lemma wageG :0 ≤ wages j x:=sum_nonneg fun i _=> norm_nonneg _
lemma tendW (x:ℝ): Continuous (wages j):=by
     letI:FiniteDimensional ℂ ↥Z:= FiniteDimensional.finiteDimensional_submodule _; exact continuous_finsetSum _ fun i hi=> (grunt i j).toContinuousLinearMap.continuous.norm -- type
variable {p q:ℕ}(α a ε η L Lb u v M1 M2 γ:ℝ)(x y:Z)(j:Axis)(P Q:BudgetPoint)(w w' r μ M W:ℝ)
local notation "F₀"=> (Fintype.card (Rings 10):ℝ)
-- M1 M2 prices per j. iterate K>0 common scaling incl /price
structure Pan (n:ℕ)(p:ℕ→Z)(Pt:ℕ→BudgetPoint) (M:Axis→ℕ→ℝ) (A:ℕ→ℝ)(V:ℕ→ℝ)(u α a ε:ℝ) : Prop where
    step : 0 <u
    high: u ≤ 1
    base i: 0 < A i
    script: 0 ≤α
    toxin:0 ≤ ε
    prim:0≤a
    story i j: i≤ n → wealth ((p i).val j).val (Pt i).threshold (A i) ≤ M j i
    credit i j: i<n→ TypeBeta u (A (i+1)) (A i) (V i * A i) α ε (ε*M j (i+1)) (Pt (i+1)) (Pt i) ((p (i+1)).val j) ((p i).val j)
    margin i j: i<n→ M j i ≤ a*(toted u ((p (i+1)).val j) (Pt (i+1)) (A (i+1))+u^11 * M j (i+1)) + wealth ((p i).val j).val (Pt i).threshold (A i)
variable {n:ℕ}{p:ℕ→Z}{Pt:ℕ→BudgetPoint}{A V:ℕ→ℝ}{Mv:Axis→ℕ→ℝ}(h:Pan n p Pt Mv A V u α a ε)
variable {K:ℕ→ℝ}(hK:0≤L)(hBp:∀ i:ℕ,0 < K i)(hT:∀ (i:ℕ),i<n → K i=L*K (i+1))
noncomputable def trunks (x:ℕ→Z)(Pt:ℕ→BudgetPoint)(A K:ℕ→ℝ)(i:ℕ)(k:Fin 4) : Z:= (K i:ℂ) • stack k (Pt i).threshold (A i) (x i)
noncomputable def nuP (k:Fin 4)(Pt:ℕ→BudgetPoint)(A V:ℕ→ℝ)(u L:ℝ)(i:ℕ):ℝ:= (L*u^(tierQ k).1)*(bud k (Pt i).threshold (V i * A i)/bud k (Pt (i+1)).threshold (A (i+1)))
local notation "XK" i:arg k:arg=> trunks p Pt A K i k
local notation "R" i:arg=> K i* Mv j i
include h hK hBp hT
lemma trunk_step (i:ℕ)(hi:i<n)(k:Fin 4) : wages j ((XK i k)- (nuP k Pt A V u L i:ℂ) • (XK (i+1) k)) ≤
    L*F₀*((if k=0 then 0 else α*u^8*wages j (XK (i+1) 0))+ 2*ε*(R (i+1))):=by
      have hp':=h.step; let Φ:=V i; let B:= bud k (Pt i).threshold (Φ*A i) /bud k (Pt (i+1)).threshold (A (i+1)); let κ:=u^(tierQ k).1 * B; let f(i):= K i; let t:= i+1; let X(i k):=stack k (Pt i).threshold (A i) (p i)
      have hh: XK i k- (nuP k Pt A V u L i:ℂ) • XK (i+1) k= (K i:ℂ) • (X i k - (κ:ℂ) • X t k):=by
             unfold trunks nuP; rw[smul_sub,smul_smul,smul_smul,hT i hi]; refine congr_arg (fun x:ℂ=> ((↑(L*K t):ℂ)) • X i k-x • X t k) ?_; change (↑((L* u^(tierQ k).1)*B):ℂ) * _= _; unfold κ; push_cast; ring
      rw [hh,wageS, Complex.norm_real,Real.norm_of_nonneg (hBp i).le]; apply (mul_le_mul_of_nonneg_left (rhythmQ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.credit i j hi) h.script h.step.le h.toxin (h.base _)) ((hBp i).le)).trans; -- ordering
      let b:=wages j (X t 0); let E:= if k=0 then 0 else α*u^8*b; let G:=wealth ((p t).val j).val (Pt t).threshold (A t); let Zκ:= Mv j t; change K i*(F₀*(E+ε*G+ ε*Zκ)) ≤ _; calc
           _ ≤ K i* (F₀*(E+ε*Zκ + ε*Zκ)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add_right (mul_le_mul_of_nonneg_left (h.story _ _ hi) h.toxin) E) _) (by positivity)) (hBp i).le
           _ = _ := by unfold trunks E; rw [hT i hi,wageS,Complex.norm_real, Real.norm_of_nonneg (hBp _).le]; change (L*K t)*(F₀*((if k=0 then 0 else α*u^8*b)+ ε*Zκ+ε*Zκ)) = L*F₀* ((if _ then 0 else α*u^8*(K t*b))+2*ε*(K t*Zκ)); split <;> ring
lemma trunk_sane (i:ℕ)(hi:i<n) : R i ≤ L*a*(∑ k:Fin 4,u^(tierQ k).1*wages j (XK (i+1) k))+L*a*u^11*(R (i+1))+∑ k:Fin 4,wages j (XK i k):=by
     have ht(i:ℕ): ∑ k:Fin 4,wages j (XK i k)=K i* wealth ((p i).val j).val (Pt i).threshold (A i):=by simp_rw[trunks,wageS, Complex.norm_real,Real.norm_of_nonneg (hBp _).le, ← Finset.mul_sum]; exact congr_arg _ (wow ..).symm
     have hx(i:ℕ): ∑ k:Fin 4,u^(tierQ k).1*wages j (XK i k)= K i*toted u ((p i).val j) (Pt i) (A i):=by simp_rw[trunks,wageS,Complex.norm_real,Real.norm_of_nonneg (hBp _).le,mul_left_comm _ (K i), ← Finset.mul_sum]; exact congr_arg _ (toteQ ..).symm
     exact (mul_le_mul_of_nonneg_left (h.margin i j hi) (hBp _).le).trans_eq (by rw [hx, ht i,hT i hi]; ring)
omit hK hT
lemma trunk_value (i:ℕ)(hi:i ≤ n): (∑ k:Fin 4,wages j (XK i k))≤ R i∧ 0≤ R i:=by
      have hz:=h.story i j hi; refine ⟨?_,mul_nonneg (hBp _).le ((wealth_ge ..).trans hz)⟩; simp_rw [trunks,wageS,Complex.norm_real,Real.norm_of_nonneg (hBp _).le, ← Finset.mul_sum,← wow]; exact mul_le_mul_of_nonneg_left hz (hBp _).le
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.trunk_value
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.trunk_step
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.trunk_sane
