import YM.Eole.Glow
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
local notation "κ"=> Keys c 6
variable (q:I→ Bool) {P:BudgetPoint} {v α b t:ℝ}
open Further.ShellBirth49.Fusing Collide
variable (o:I→Site c)(p:J→Site c)
-- E raw footprint and common extensions
local notation "M"=> Patio ((Keys c 6)⊕Spine I)
local notation "Mt"=> Patio ((Keys c 6)⊕Spine J)
local notation "λt"=>W.flag q
variable (old:E→Support c)(a:E⊕K→Support c)(f:E⊕K→ Grid c→ Patio ((Keys c 6)⊕Spine I))(z:E⊕K→ℝ)
local notation "P₀"=> Grid c
set_option quotPrecheck false
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
variable {ν w B' Ω δ y:ℝ}
abbrev swatch (i:E⊕K):Support c:= Sum.elim (fun _=>∅) (fun j=>(Y j).inv) i
local notation "gp"=> QCD.GasP.taxed (swatch (E:=E) Y) z w
open Push.AbsoluteSums.Trees
variable (hz:Ready a P.B (QCD.GasP.taxed (swatch Y) z w) α ν b δ)
open Push.AbsoluteSums.Trees -- Ready
variable (h0:0≤ α)(hv:1≤ w)(hT:0<t)
include h0 hv hz hT
lemma revenues {D:Type} (i:D↪Finset (E⊕K)) (hh:D→Support c)(hr:∀ j,hh j=flagsOf Y (i j))(hw:∀ k,Ac.Spark a (i k)):
  Ac.Hit (shore a ∘ i) P.B (QCD.GasP.taxed hh (fun j:D=>∏ t∈i j,z t) w) α (ν*(1-δ)⁻¹) := by
     intro x; let r x':= touches a P.B (QCD.GasP.taxed (swatch Y) z w) α x x'; have hW:= touch_tail a P.B hz x 0; simp only [Nat.zero_le,ite_true,pow_zero,mul_one] at hW; have hX:= budget_pull i i.injective hW; let τ:= α; have hk:0≤w:=zero_le_one.trans hv; have he(j:D) : flagsOf Y (i j)= (i j).biUnion (swatch Y):=by
        ext x; simp only [flagsOf,mem_toRight,mem_biUnion]; constructor; rintro ⟨k,hp,h⟩; exact ⟨Sum.inr k,hp,h⟩; rintro ⟨(k|k),hp,h⟩; exact False.elim (notMem_empty _ h); exact ⟨k,hp,h⟩
     have hn:=positiveZ W g Y q o p old a f z h hT
     refine budget_mono hX (fun j=>ite_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hk _) (prod_nonneg fun _ _=>hn _)) (Real.exp_pos _).le) le_rfl) fun j=> ?_
     split; swap; · exact hX.1 _
     next hp=> let S:=i j; change _ ≤ if Ac.Spark _ S∧ _ then _ else _; rw [if_pos ⟨hw j,hp⟩,prod_mul_distrib]; apply mul_le_mul ?_ _ (Real.exp_pos _).le (prod_nonneg fun _ _=> mul_nonneg (pow_nonneg hk _) (hn _))
               · unfold taxed; rw [prod_mul_distrib,prod_pow_eq_pow_sum]; apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _=> hn _); rw[hr,he]; exact pow_le_pow_right₀ hv card_biUnion_le
               unfold currency; rw [← Real.exp_sum,← mul_sum,← Nat.cast_sum]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Ac.cover _ _ (hw j))) h0)
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.revenues
