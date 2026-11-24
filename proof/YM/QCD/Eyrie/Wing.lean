import YM.QCD.Eyrie.Spire
import YM.MultiNext.VACUUM_STABILITY.Hits

/-! # price at location carried by analytic ownership. one width uniform over repeat. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Lat Kit Cost Finset Run Revolve Metric Push.Uniform
open YM.Multi.Vacuum.Hits
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical
variable {f : Side} {u r a : ℝ} {B : ℕ}
def amplitude (B:ℕ):= ((stride B:ℕ):ℝ)⁻¹
lemma amplitude_pos (B):0<amplitude B:=inv_pos.mpr (by unfold stride; positivity)
lemma purchases {M: Grid f→Sheet f} (h : Own f r 1 B M u) (hp:0<r)(i j:Row f)(U:Grid f):
    ‖M U i j‖ ≤ u*Decay (amplitude B) i.1 j.1:=by
  obtain ⟨A,C,H⟩:= h
  rcases i with ⟨i,v⟩; rcases j with ⟨j,w⟩
  let Z:=Decay (amplitude B) i j
  have he L : ‖A i j L (settled U)‖≤rent 1 B L*C i j L*Z:=by
    have h := H.crop i j L; apply le_trans (h.2.2.2.1 (settled U) (citizenship f hp U))
    by_cases he : C i j L=0; · simp [he]
    have H := h.2.1 he
    rw [mul_right_comm]; apply le_mul_of_one_le_left h.1; unfold rent Z Decay
    rw [← Real.exp_add]; refine Real.one_le_exp ?_
    have hx:= distance L B H.1 H.2; have hh : (separation i j:ℝ) ≤ (Lattice.coverNumber B L:ℝ)*stride B := by exact_mod_cast hx
    unfold amplitude
    have ht : 0<(stride B:ℝ):=by unfold stride; positivity
    nlinarith only [hh,(show 0≤((stride B:ℝ)⁻¹) by positivity), inv_mul_cancel₀ ht.ne', mul_le_mul_of_nonneg_right hh (show 0 ≤ ((stride B:ℝ)⁻¹) by positivity)]
  change ‖Run.cell (M U) i j v w‖ ≤ u*Z
  apply (north ..).trans; rw [← H.sells i j]
  apply (norm_sum_le ..).trans; apply (sum_le_sum fun a _=> he a).trans; rw [← sum_mul]; apply mul_le_mul_of_nonneg_right _ (decay_pos ..).le
  apply le_trans _ (H.spends i); apply single_le_sum ?_ (mem_univ j); intro k _; exact sum_nonneg fun z _=>mul_nonneg (fair ..).le (H.crop i k z).1
end YM.QCD.Eyrie
