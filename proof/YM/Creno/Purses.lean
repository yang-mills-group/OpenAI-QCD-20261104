import YM.Creno.Kuna
import YM.Creno.Fam
import YM.Bwana.Schar
/- Pair-painting.Y possible member χ inactive, birth otherwise. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Eole.Triple
variable {I:Type} [Fintype I] (q:I→Bool)
local notation "Zs"=> I × Fin 3
local notation "Js"=> I × Bool
variable (α β Y U S M P A:ℝ) (p:I × Fin 3→ℝ) -- Wt.C β sign.N. w0 2*(Vrequest α χ);
abbrev lenseC (α β:ℝ)(x:I × Bool):ℝ:= if x.2 then β else α
variable {α β U S M A P Y}
local notation "Q"=> lenseC (I:=I)
variable (hM:0<M)(hP:0<P)(hu:0 <U)
-- P,C budgets positive.i active. Cost P*N? define
lemma mintR (ha:0 ≤ α): α ≤Y→ |α|≤ Y:=by rw [abs_of_nonneg ha]; exact id
-- avoid `omit`. optional later.One input v0 y1 y2.
include hM hP hu
lemma receiptPair (hx:∀ j:I,p (j,0) ≤ M)(hy:∀ j:I,p (j,1) ≤ P)(hb:∀ j:I, |β| * p (j,2) ≤ U)(hα: |α| * M * P ≤ U^2): ∃ τ:Zs→ℝ,(∀ j:Js, (((pack₃ I).arm j).map τ).prod= Q α β j) ∧∀ j:Zs,|τ j| * p j ≤ U:=by
     let t:= U/M; have ht:0<t:=div_pos hu hM
     let w:=α/t; let τ(j:Zs):ℝ:= ![t,w,β] j.2
     have ht2:|w| *P ≤ U:=by unfold w; rw[abs_div,abs_of_pos ht,div_mul_eq_mul_div]; apply (div_le_iff₀ ht).2; unfold t; rw [←mul_div_assoc]; apply (le_div_iff₀ hM).2; rw [mul_right_comm,pow_two] at hα; exact hα
     refine ⟨τ,?_,?_⟩
     · rintro ⟨a,b⟩; cases b <;> simp only[pack₃,lenseC,Bool.false_eq_true,↓reduceIte,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one] -- fin_cases
       · change t*w=_; rw[mul_comm t]; exact div_mul_cancel₀ α ht.ne'
       rfl
     rintro ⟨j,b⟩; fin_cases b
     · change |t| * p _≤ _; rw [abs_of_pos ht]; exact (mul_le_mul_of_nonneg_left (hx j) ht.le).trans_eq (div_mul_cancel₀ _ hM.ne')
     · change |w| * p _ ≤ _; exact (mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)).trans ht2
     exact hb j
end Eole.Triple
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Eole.Triple.receiptPair
