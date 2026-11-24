import YM.QCD.Step.Letters
import YM.Corona.Halo

/-! Tube calculus, holomorphic near every settled field uniformly -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Finset Filter Lat Wilson Lattice Cost Metric Kit Function
open scoped Matrix Matrix.Norms.L2Operator Topology BigOperators ContDiff
variable {n : Side} {ι D E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup D] [NormedSpace ℂ D]

lemma wind {f : D → E} {x y : D} {B R : ℝ} (hR : 0<R) (hf : ∀ x' ∈ ball x R,DifferentiableAt ℂ f x')
    (h : ∀ z ∈ ball x R, ‖f z‖ ≤ B) (hy : y∈ball x (R/2)):
    ‖fderiv ℂ f y‖ ≤ B / (R/2):=by
  have hr : 0<R/2:=half_pos hR
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg ((norm_nonneg _).trans (h x (mem_ball_self hR))) hr.le)
  intro v hv
  let g : ℂ → D := fun t => y + t • v
  have hd : HasDerivAt g v 0 := by simpa [g] using! (((hasDerivAt_id' (0:ℂ)).smul_const v).const_add y)
  have he : g 0=y:=by simp[g]
  have hc := (hf (g 0) (by rw [he]; exact ball_subset_ball (half_le_self hR.le) hy)).hasFDerivAt.comp_hasDerivAt 0 hd
  rw [he] at hc; rw [← hc.deriv]
  have hu (t) (ht : t∈closedBall (0:ℂ) (R/2)): g t∈ball x R:=by
    have hp : dist (g t) y ≤ R/2:=by simpa [g,dist_eq_norm,norm_smul,hv,Metric.mem_closedBall] using ht
    rw [mem_ball] at hy ⊢; linarith [dist_triangle (g t) y x]
  have hh (z) (hz : z∈closedBall (0:ℂ) (R/2)): DifferentiableAt ℂ (f∘g) z:= (hf (g z) (hu _ hz)).comp z (by unfold g; fun_prop)
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ⟨fun z hz=> (hh z (ball_subset_closedBall hz)).differentiableWithinAt,?_⟩ fun z hz=> h _ (hu _ (sphere_subset_closedBall hz))
  intro z hz; exact (hh z (closure_minimal ball_subset_closedBall isClosed_closedBall hz)).continuousAt.continuousWithinAt

lemma frosty [CompleteSpace E] (f : ι → D → E) {X : Set D} (hX : IsOpen X)
    {p : ι → ℝ} (hf : ∀ i x, x∈X → DifferentiableAt ℂ (f i) x) (hu : Summable p)
    (h : ∀ i z, z∈X → ‖f i z‖ ≤ p i) (x : D) (hx : x∈X) : DifferentiableAt ℂ (fun z=> ∑' i, f i z) x:=by
  obtain ⟨r,hr,H⟩ := Metric.mem_nhds_iff.mp (hX.mem_nhds hx)
  letI : NormedSpace ℝ D := NormedSpace.restrictScalars ℝ ℂ D
  have hh : 0<r/2:=half_pos hr
  have ht (y) (hy:y∈ball x (r/2)): y∈X:= H (ball_subset_ball (half_le_self hr.le) hy)
  exact (hasFDerivAt_tsum_of_isPreconnected (hu.div_const (r/2)) isOpen_ball
    (convex_ball x (r/2)).isPreconnected
    (fun i z hz=> ((hf i) z (ht z hz)).hasFDerivAt)
    (fun i y hy=> wind hr (fun z hz=>hf i z (H hz)) (fun z hz=>h i z (H hz)) hy)
    (mem_ball_self hh)
    (.of_norm_bounded hu (fun i => h i x hx)) (mem_ball_self hh)).differentiableAt

def Kingdom (f : Side) (δ : ℝ) : Set (Pulse f) := ⋃ U:Grid f, ball (settled U) δ
lemma country (f : Side) (δ : ℝ) : IsOpen (Kingdom f δ):=isOpen_iUnion fun _=>isOpen_ball
lemma citizenship (f : Side) {δ : ℝ} (h : 0<δ) (U : Grid f) : settled U ∈ Kingdom f δ := Set.mem_iUnion.mpr ⟨U,mem_ball_self h⟩

def rent (b : ℝ) (B : ℕ) (S : Support n) := Real.exp (b*coverNumber B S)
lemma fair (b : ℝ) (B : ℕ) (S : Support n): 0<rent b B S:=Real.exp_pos _
lemma market {b : ℝ} (hb : 0≤b) (B : ℕ) (S : Support n): 1 ≤ rent b B S:= Real.one_le_exp (by positivity)
lemma pooled {b : ℝ} (hb : 0≤b) (B : ℕ) {S T : Support n} {x : Site n} (hx : x ∈ S) (hv : x∈T) : rent b B (S∪T)≤rent b B S*rent b B T:=by
  unfold rent; rw [← Real.exp_add,← mul_add]; apply Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left _ hb); exact_mod_cast Corona.meets_sum hx hv B
end YM.QCD.Run
