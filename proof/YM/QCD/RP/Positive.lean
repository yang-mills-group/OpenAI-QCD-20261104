import YM.QCD.RP.House
import YM.QCD.Lattice.Stability

/-!
# Finite QCD cut has link-plane OS positivity

In complex order, depends on parity algebra and a gauge invariant insertion,
no sign-of-determinant assumption in this part of the proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lattice Wilson Grass Lat NormedSpace Function Slice MeasureTheory YM.Analysis Filter
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology ComplexOrder
variable {n : Side} {R : Cells.Cut n} {F : ℕ} {C : Lat.Cut n F}
local notation "O" => (Open R su)

lemma all_rays (h : R.kind=.link) {x : Fields n F} (hx : Matinee R x) (s : O → Dirac (Lamp R F)) :
    NNKernel fun X Y => ber (Modes n F) (x * RP.hit R (s Y) (s X)) := by
  induction hx generalizing s with
  | zero =>
    intro m y; simp only [zero_mul,map_zero]; exact Matrix.PosSemidef.zero
  | ray p u H =>
    simp_rw [shuffle _ _ _ _ H H, RP.hit,overlap R h]
    let k := NNKernel.gram (fun x : O => ber (Lamp R F) (u*s x))
    intro m f; exact (k m f).transpose
  | add _ _ ih₁ ih₂ => simp_rw [add_mul,map_add]; exact (ih₁ s).plus (ih₂ s)

lemma gauge_rays (h : R.kind=.link) {β : ℝ} (hb : 0 ≤ β) : NNKernel fun X Y : O => (bare β (RP.clear R X Y):ℂ) := by
  simp_rw [RP.clear, includes, Link.outer h]
  let f := fun X : O => (area R β 1 X : ℂ)
  have ha (X Y : O) : (↑(area R β 1 X*area R β 1 Y) : ℂ)=star (f X)*f Y := by simp [f]
  change NNKernel fun X Y =>
    ((area R β 1 X * area R β 1 Y * (Slice.weight R.pos β (Link.first h Y) (Link.first h X) 1 *
      Slice.weight R.pos β (Link.last h X) (Link.last h Y) 1) : ℝ) : ℂ)
  have h₁ : NNKernel fun X Y : O => ((Slice.weight R.pos β (Link.first h Y) (Link.first h X) 1 : ℝ) : ℂ) := by
    intro m i; exact ((positive_weight R.pos hb) m ((Link.first h) ∘ i)).transpose
  refine ((NNKernel.gram f).times (h₁.times ((positive_weight R.pos hb).titled (Link.last h)))) |> fun H => ?_
  have he (X Y : O) : ∀ a b : ℝ, ((area R β 1 X * area R β 1 Y * (a*b) : ℝ):ℂ)=star (f X)*f Y * ((a:ℂ)*(b:ℂ)) := by
    intro a b; simp [f]
  simp_rw [he]; exact H

lemma fence_pos (h : R.kind=.link) (T : Matches C R) (hb : 0≤ C.β) (x : Insertion n F) (H : Sided R x) : NNKernel
    (fun X Y : O => C.rate (reflect R x*x) (RP.clear R X Y)) := by
  obtain ⟨s,-,ht,hp⟩ := H
  let g : O → Dirac (Lamp R F) := fun X => s (chain R.pos (reader R 1 X))
  let S := fun X : O => exp (fence C h X)
  have h₁ (X) : Grass.Hom false (exp (fence C h X)) := by
    change grade (exp _)=exp _; rw [map_weight,(show grade (fence C h X)=_ from fence_even ..)]
  have he (X Y : O) : (reflect R x*x) (RP.clear R X Y)=RP.hit R (g Y) (g X) := by
    rw [ContinuousMap.mul_apply, reflects,hp,hp]
    unfold RP.clear; rw [ht _ _ (first_eye R _),ht _ _ (second_eye R _)]; rfl
  unfold Lat.Cut.rate
  simp only [ContinuousMap.mul_apply (f:=Lat.Cut.insertD _)] -- check
  have hu (X Y : O) : RP.hit R (exp (fence C h Y)) (exp (fence C h X)) * RP.hit R (g Y) (g X) = RP.hit R (S Y*g Y) (S X*g X) := shuffle _ _ _ _ (h₁ _) (h₁ _)
  simp_rw [he,dress h T,mul_assoc,hu]
  exact (gauge_rays h hb).times (all_rays h (joint_even F h).2 (fun X => S X*g X))

/-- Link-cut raw positivity. No homogeneity/evenness required of the probe.
`x` may be Grassmann odd. -/
theorem raw_positive (h : R.kind=.link) (T : Matches C R) (hL : 2≤ R.half.val) (hb : 0≤ C.β)
    (x : Insertion n F) (H : Sided R x) (hi : Invariant x) : 0 ≤ C.raw (reflect R x*x) := by
  let f := reflect R x*x
  let j := C.rate f
  have hg : GaugeInvariant j := fun k U => (transforms k C f U).symm.trans (by rw [show transform k f=f from invariant_mul _ _ (reflect_invariant R x hi) hi k])
  change 0 ≤ ∫ U, j U ∂prior su n
  rw [cleared h hL _ (C.rate_cont _) hg]
  have hk : Continuous (fun z : Free R => j (RP.clear R z.1 z.2)) := (C.rate_cont _).comp clear_cont
  haveI : @BorelSpace O (MetricSpace.toPseudoMetricSpace (α:=O)).toUniformSpace.toTopologicalSpace (inferInstance : MeasurableSpace _) := instBorelSpaceOpen R
  haveI : @SecondCountableTopology O (MetricSpace.toPseudoMetricSpace (α:=O)).toUniformSpace.toTopologicalSpace := instSecondCountableTopologyOpen _
  haveI : @CompactSpace O (MetricSpace.toPseudoMetricSpace (α:=O)).toUniformSpace.toTopologicalSpace := (inferInstance : CompactSpace O)
  have hv := NNKernel.integrated (X:=O) (fieldM su R) (fence_pos h T hb x H) hk (f:=fun _ : O => 1)
    measurable_const (C:=1) (by simp)
  simp only [star_one, mul_one] at hv; exact hv

lemma reflected_positive (h : R.kind=.link) (T : Matches C R) (hL : 2≤ R.half.val) (hb : 0≤ C.β)
    (hp : 0<C.partitionR) (x : Insertion n F) (H : Sided R x) (hi : Invariant x) : 0 ≤ C.average (reflect R x*x) := by
  change 0 ≤ (C.partitionR:ℂ)⁻¹ * _
  exact mul_nonneg (by positivity) (raw_positive h T hL hb _ H hi)
end YM.QCD.RP
