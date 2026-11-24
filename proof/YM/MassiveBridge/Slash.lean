import YM.MassiveBridge.Differentials
/-!
# Analytic Boost postulate discharged here from Euclidean structure

Reuse single-parameter argument of YM/Work/C07.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Rotate
open Set Filter Function Analysis MeasureTheory LineDeriv Mink Complex
open Boundary hiding Fields Surface Waves
open Work.C07 (orbit integral_orbit orbit_image foldE fold_smooth fold_derivative testField test_zero_off test_one test_imag analytic_integral incline_cont stretchY scaledTimes scaled_imag scaled_one scaled_strict_imag)
open Bid (inclined realTerm)
open Spinor
open MassiveTwoEstimates
open scoped Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {Q:Massive.Sequence} {P:Calibration Q} {X:Massive.Fields} {S:X.Kernel}
variable {Y:Waves X} {n:ℕ}
def allowed (K : Set (Points n)) (y : Heights n) : Set ℂ :=
    {z | ∀ p ∈ K, scaledTimes y z p ∈ strict n}

lemma scaled_cont (y : Heights n) :
    Continuous (uncurry (scaledTimes y)) := by
  change Continuous fun p : ℂ × Points n => scaledTimes y p.1 p.2
  unfold scaledTimes; fun_prop

lemma allowed_open {K : Set (Points n)} (y : Heights n) (hK : IsCompact K) : IsOpen (allowed K y) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let W := uncurry (scaledTimes y) ⁻¹' strict n
  have hW : ({z} : Set ℂ) ×ˢ K ⊆ W := by
    rintro ⟨p,q⟩ ⟨hp,hq⟩
    exact (show p=z from hp).symm ▸ hz q hq
  obtain ⟨t,s,ht,-,htz,hsK,H⟩ := generalized_tube_lemma isCompact_singleton hK
    ((open_strict n).preimage (scaled_cont y)) hW
  exact ⟨t, fun a ha b hb => H (mk_mem_prod ha (hsK hb)), ht, htz (mem_singleton z)⟩

lemma allowed_convex (K : Set (Points n)) (y : Heights n) : Convex ℝ (allowed K y) := by
  rw [convex_iff_forall_pos]
  intro z hz r hr a b ha hb hab p hp i j hij
  have he (k : Fin n) : (scaledTimes y (a • z + b • r) p k).im =
      a * (scaledTimes y z p k).im + b * (scaledTimes y r p k).im := by
    simp only [scaledTimes, add_im, mul_im, ofReal_re, ofReal_im, real_smul,
      I_re, I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one]
    linear_combination -(y k)*hab
  change (scaledTimes y _ p i).im < (scaledTimes y _ p j).im
  rw [he, he]
  exact add_lt_add (mul_lt_mul_of_pos_left (hz p hp hij) ha) (mul_lt_mul_of_pos_left (hr p hp hij) hb)

lemma allowed_real (K : Set (Points n)) {y : Heights n} (hy : y ∈ east n) (z : ℝ) :
    (z : ℂ) ∈ allowed K y := fun p _ i j h => by simpa [scaledTimes] using hy h

lemma error_analytic (hr : Y.Region S) {K : Set (Points n)} (hK : IsCompact K)
    (a : SpaceAxis) (y : Heights n) (v : Fin n → X.W) (f : Joint n) :
    AnalyticOnNhd ℂ (fun z => ∫ p in K, errorTerm Y a y v f z p) (allowed K y) := by
  let U := allowed K y
  apply analytic_integral hK _ (allowed_open y hK)
  · have ht : Continuous (fun p : Points n => trace p) := by unfold trace; fun_prop
    have hu (q : Fin n → X.W) : ContinuousOn (fun p : ℂ × Points n => seen Y q y p.1 p.2)
        (U ×ˢ K) :=
      (hr.together n q).comp ((scaled_cont y).prodMk (ht.comp continuous_snd)).continuousOn
        (by rintro ⟨z,p⟩ ⟨hz,hp⟩; exact ⟨hz p hp, mem_univ _⟩)
    change ContinuousOn (fun p : ℂ × Points n => errorTerm _ _ _ _ _ p.1 p.2) _
    have hF : Continuous (fun p : ℂ × Points n => testField a y p.1 f p.2) := by
      unfold testField; refine continuous_finsetSum _ fun i _ => ?_
      have ht (b : Axis) : Continuous (fun p : ℂ × Points n => realTerm i b f p.2) :=
        (realTerm i b f).continuous.comp continuous_snd
      have hi : Continuous (fun p : ℂ × Points n => scaledTimes y p.1 p.2 i) :=
        (continuous_apply i).comp (scaled_cont y)
      exact Continuous.add ((by fun_prop : Continuous fun p : ℂ × Points n => ((p.2 i a.castSucc:ℝ):ℂ)).mul (ht timeAxis))
        ((continuous_fst.mul hi).mul (ht a.castSucc))
    unfold errorTerm
    exact ((hu _).mul hF.continuousOn).sub ((continuous_fst.continuousOn.mul
      (continuousOn_finsetSum _ fun i _ => hu (update v i (kick X a (v i))))).mul
      (f.continuous.comp continuous_snd).continuousOn)
  intro p hp
  have hk : Differentiable ℂ (fun z => scaledTimes y z p) := by
    unfold scaledTimes; fun_prop
  have hs (q : Fin n → X.W) : DifferentiableOn ℂ (fun z => seen Y q y z p) U :=
    (hr.hol n q (trace p)).comp hk.differentiableOn fun _ hz => hz p hp
  have hT : Differentiable ℂ (fun z => testField a y z f p) := by
    unfold testField; unfold scaledTimes; fun_prop
  unfold errorTerm
  apply DifferentiableOn.sub ((hs _).mul hT.differentiableOn)
  exact (differentiableOn_id.mul (DifferentiableOn.fun_sum fun i _ => hs
    (update v i (kick X a (v i))))).mul_const _

theorem error_one (E:X.System P) (H:Fields.Euclidean S)
    (hr : Y.Region S) (a : SpaceAxis) (y : Heights n) (hy : y ∈ east n)
    (v : Fin n → X.W) (f : Joint n) (hK : HasCompactSupport ⇑f) :
    (∫ p in tsupport f, errorTerm Y a y v f 1 p) = 0 := by
  let K := tsupport f
  let U := allowed K y
  have h₀ : (0 : ℂ) ∈ U := by simpa using allowed_real K hy 0
  have h₁ : (1 : ℂ) ∈ U := by simpa using allowed_real K hy 1
  apply (error_analytic hr hK a y v f).eqOn_zero_of_preconnected_of_frequently_eq_zero
    ((allowed_convex K y).isPreconnected) h₀ _ h₁
  intro hh
  have ht : Tendsto (fun w : ℝ => (w : ℂ)*I) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun w : ℝ => (w : ℂ)*I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    filter_upwards [self_mem_nhdsWithin] with w hw
    change _ ≠ _; simp [ne_of_gt (show 0<w from hw)]
  have hK' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ U :=
    Eventually.filter_mono nhdsWithin_le_nhds ((allowed_open y hK).mem_nhds h₀)
  obtain ⟨w,hw,hU⟩ := (ht.eventually (hh.and hK')).exists
  exact hw (error_imag E H hr a y v f w hK hU)

lemma compact_boost (E:X.System P) (H:Fields.Euclidean S)
    (hr : Y.Region S) (hB : Y.Bounds) (a : SpaceAxis) (y : Heights n) (hy : y ∈ east n)
    (v : Fin n → X.W) (f : Joint n) (hK : HasCompactSupport ⇑f) :
    (∑ i, Y.psi (update v i (kick X a (v i))) y f) = Y.psi v y (inclined a y f) := by
  have he (p : Points n) (hp : p ∉ tsupport f) : errorTerm Y a y v f 1 p = 0 := by
    rw [errorTerm, test_zero_off a y _ f hp, image_eq_zero_of_notMem_tsupport hp]
    ring
  let f' := inclined a y f
  let q (i : Fin n) (p : Points n) := seen Y (update v i (kick X a (v i))) y 1 p * f p
  have hq (q : Fin n → X.W) (p : Points n) : Y.restricted q y p = seen Y q y 1 p := by rw [seen, scaled_one]; rfl
  have hI (i) : Integrable (q i) := by
    simp_rw [q, ← hq]; apply hB _ _ _ hy
  have hJ : Integrable (fun p => seen Y v y 1 p * f' p) := by
    simp_rw [← hq]; apply hB _ _ _ hy
  have h₁ := error_one E H hr a y hy v f hK
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero he] at h₁
  simp_rw [errorTerm, test_one, one_mul, Finset.sum_mul] at h₁
  change (∫ p, seen Y v y 1 p * f' p - ∑ i, q i p) = 0 at h₁
  rw [integral_sub hJ (integrable_finsetSum _ fun i _ => hI i),sub_eq_zero,
    integral_finsetSum Finset.univ (fun i _ => hI i)] at h₁
  simp_rw [Waves.psi, hq]; exact h₁.symm

lemma continuous_test (hB : Y.Bounds) (ha : Y.Along) (hl : Y.Lines) (hb : Y.Breathes)
    (y : Heights n) (hy : y ∈ east n) (q : Fin n → X.W) : Continuous (Y.psi q y) := by
  obtain ⟨W,hW⟩ := Y.seeks hB ha hl hb y (bigger hy)
  haveI : (𝓝[east n] y).NeBot := awaits (bigger hy)
  have he (f : Joint n) : Y.psi q y f = W q f :=
    tendsto_nhds_unique (ha n q f y hy) (hW q f)
  rw [funext he]; exact (W q).continuous

def Boosty (Y : Waves X) : Prop := ∀ n (v:Fin n → X.W) a (f: Joint n) y, y∈east n → ∑ i, Y.psi (update v i (kick X a (v i))) y f = Y.psi v y (inclined a y f)
theorem analytic_boost (E:X.System P) (H:Fields.Euclidean S) (hr:Y.Region S) (hb:Y.Breathes) : Boosty Y :=by
  have hB:=Waves.bounds hr hb; have hl:=Waves.lines hr hb; have ha:=Waves.along hr hb
  intro n v a f y hy
  let A (u : Joint n) := ∑ i, Y.psi (update v i (kick X a (v i))) y u
  let B (u : Joint n) := Y.psi v y (inclined a y u)
  have hA : Continuous A :=
    continuous_finsetSum _ fun i _ => continuous_test hB ha hl hb y hy _
  have hX : Continuous B :=
    (continuous_test hB ha hl hb y hy _).comp (incline_cont a y)
  have he (k : ℕ) : A (Probe.cap k f) = B (Probe.cap k f) :=
    compact_boost E H hr hB a y hy v (Probe.cap k f) (Probe.finite_cap k)
  have hz : Tendsto (fun k : ℕ => A (Probe.cap k f)) atTop (𝓝 (A f)) :=
    (hA.tendsto f).comp (Probe.persistent f)
  simp_rw [he] at hz
  exact tendsto_nhds_unique hz ((hX.tendsto f).comp (Probe.persistent f))

end YM.Massive.Bridge.Rotate
