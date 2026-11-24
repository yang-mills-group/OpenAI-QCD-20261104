import YM.Next.ROTATIONS.Energy
import YM.Gust.Cav.OSlices
/- Variant of YM.Next.ROTATIONS.Energy, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Function Filter Set Metric MeasureTheory Measure Complex Boundary Probe Nodes
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ENNReal
/-- Shape bounded below near zero. Using just this particular shape in the
final weighted estimates, integrates all dyads incl the E=0 endpoint. -/
private def ball_center : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
open OS Row
variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i)
theorem surface (H : S.Hierarchy) (A : Weight L) (h : Pressed i A) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ D : ℕ, ∀ (m : ℕ), D≤2*m → ∀ (f : Profile), Ends f → Plus f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1≤s → ∀ w : ℝ, 0<w → Room (width w f) s →
        let g := fun p : E4 => Mlamp m s (width w f) (p i) * ‖p j‖^(2*k)
        Integrable g (ν V A) ∧ (∫ p, g p ∂ν V A) ≤ C*(w⁻¹+s^D) := by
  obtain ⟨D,hD⟩ := pay_moment V H A h j hj k
  let μ := ν V A
  let M (p : E4) := ((1+p i)⁻¹)^D * ‖p j‖^(2*k)
  have hu : ∀ᵐ p : E4 ∂μ, 0≤p i := before V A
  have hz : 0 ≤ ∫ p,M p ∂μ := integral_nonneg_of_ae (hu.mono fun x hx => show 0 ≤ ((1+_)⁻¹)^D * ‖x j‖^(2*k) by positivity)
  refine ⟨D,fun m hm f hf hp => ?_⟩
  obtain ⟨B,hB,hh⟩ := shelf m D hm f hf hp
  refine ⟨B*(∫ p,M p ∂μ),mul_nonneg hB hz,fun s hs w hw hr => ?_⟩
  intro g
  let c := B*(w⁻¹+s^D)
  have he : ∀ᵐ p ∂μ,g p≤c*M p := hu.mono (fun x hx =>
    (mul_le_mul_of_nonneg_right (hh s hs w hw hr (x i) hx) (pow_nonneg (norm_nonneg _) _)).trans_eq (mul_assoc ..))
  have hM : Integrable (fun p => c*M p) μ := hD.const_mul c
  have hg : Integrable g μ := by
    apply hM.mono'
    · have hv := lamp_m m s (width w f); unfold g; apply Measurable.aestronglyMeasurable; fun_prop
    filter_upwards [hu,he] with x hx hy
    rwa [Real.norm_of_nonneg (mul_nonneg (lamp_sign m s (width w f) (x i) (by linarith) hx (hf.width w) (hp.tall w hw.le) hr) (pow_nonneg (norm_nonneg _) _))]
  exact ⟨hg,(integral_mono_ae hg hM he).trans_eq (by rw [integral_const_mul]; exact mul_right_comm ..)⟩
end YM.Spiral.Outer

