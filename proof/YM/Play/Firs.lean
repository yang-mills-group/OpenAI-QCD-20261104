import YM.Play.Lich
import YM.MassiveQCD.Plate.Shift
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open Function MeasureTheory Filter Finset QCD -- order
open QCD QCD.Grass QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge Cupola Ribbon
open Matrix QCD.Anomaly QCD.Bera
open scoped BigOperators Topology Classical Matrix
variable {I J:Type}[Fintype I][Fintype J]
variable (v t:ℝ) (s:ℕ) (z:Patio (J ⊕ Spine I))
local notation "Ψ"=> Plate.turn I v
lemma turnBills (hx: z∈ vaultS univ s)(hp: ‖v-1‖ ≤ t)(he:‖v‖ ≤ 2) : Ψ z∈vaultS univ s ∧ ‖Ψ z-z‖ ≤ s*t*(2:ℝ)^s*‖z‖:=by
   let Q:= Matrix.diagonal (fun i:J=>(v:ℂ)); let P:= breezeP (Spine I) Q; have h(z): ((Plate.turn I v (D:=J)) z).val= changeVars P z.val:= (shipsT (Spine I) Q z.val).symm
   have hm: z.val∈Rim univ s:=hx; refine ⟨(show (Ψ z).val ∈ _ from (h z).symm ▸ Rim.patched P (fun _ _ _ _=> mem_univ _) hm),?_⟩
   have hv:bills P univ 2:=by
       rintro (i|i) _
       · rw [Fintype.sum_sum_type]; simp only [P,Q,breezeP,Matrix.fromBlocks_apply₁₁,Matrix.diagonal_apply,fromBlocks_apply₁₂,Matrix.zero_apply,norm_zero,sum_const_zero,add_zero]; simpa only [apply_ite norm,norm_zero,Fintype.sum_ite_eq,Complex.norm_real] using he -- he wrong orientation
       rw [Fintype.sum_sum_type]; simp [P,breezeP,Matrix.one_apply,apply_ite norm]
   have hu : bills (1:Matrix (J ⊕Spine I) (J ⊕Spine I) ℂ) univ 2 := by intro i _; simp [Matrix.one_apply,apply_ite norm]
   have h0:0 ≤ t:=(norm_nonneg _).trans hp
   have hV : bills (P-1) univ t:=by
       rintro (i|i) _; rw [Fintype.sum_sum_type]; simp only [Matrix.sub_apply,P,Q,breezeP,fromBlocks_apply₁₁,fromBlocks_apply₁₂,Matrix.one_apply, Matrix.diagonal_apply,Matrix.zero_apply,Sum.inl_ne_inr, Sum.inl.injEq,if_false, sub_zero,norm_zero,sum_const_zero,add_zero]; convert! hp using 1; rw [sum_eq_single i]; · simp [← Complex.ofReal_one,← Complex.ofReal_sub]
       · intro j _ hj; simp [Ne.symm hj]
       · simp
       rw [Fintype.sum_sum_type]; simp [P,Q,breezeP, Matrix.one_apply,h0]
   change ‖((Ψ z).val - z.val)‖ ≤ s*t*(2:ℝ)^s*‖z.val‖; rw [h]; simpa only [change_one, AlgHom.id_apply] using sendsDiff P 1 hm hv hu (by norm_num) hV h0
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.turnBills
