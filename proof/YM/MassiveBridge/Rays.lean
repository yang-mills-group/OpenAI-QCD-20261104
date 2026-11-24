import YM.MassiveBridge.Covariance
import YM.Work.C05
import YM.Work.C06
/-!
# Frequency support of the continued distributions in the full tubes

A translation/boost result at operator level will only need momentum cone;
here we already need it on the several-point distributions, before construction
(for locality). Reuse YM temporal support argument C05,C06,Closing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Set Filter Function MeasureTheory Distribution Mink Complex
open Boundary hiding Surface Waves Fields
open Mink.Poincare (togetherL)
open Work.C05 (tendsto_exp_slope clock_hat continuous_of_tendsto_slope)
open Work.C06 (lift_falls)
open scoped Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius FourierTransform InnerProductSpace
variable {Q:Sequence} {P:Calibration Q} {X:Massive.Fields} {S:X.Kernel} (F:Waves X)
variable {n:ℕ} {v : Fin n → X.W}
namespace Waves
def during (W: Surface X) := ∀ (n:ℕ) (v:Fin n→X.W)(y:Heights n), y ∈ east n →∀ f : Joint n, ∀ h : HasCompactSupport ⇑f,
    Distn.fourier (W.W n v) f=F.psi v y (Probe.hat (lifts (dawn y) f h))
def psiL (h : F.Bounds) (v : Fin n → X.W) (y : Heights n) (hy : y ∈ east n) : Joint n →ₗ[ℝ] ℂ where
  toFun := F.psi v y
  map_add' f g := by
    unfold Waves.psi; rw [← integral_add (h n v y hy f) (h n v y hy g)]
    congr 1; ext x; exact mul_add ..
  map_smul' a f := by
    change F.psi v y (a • f) = a • F.psi v y f
    unfold Waves.psi; rw [← integral_smul]; congr 1; ext x; exact mul_smul_comm a _ (f x)

lemma tendsto_psi (hb : F.Bounds) (ha : F.Along) (hl : F.Lines) (hp : F.Breathes)
    {Z : Type*} {l : Filter Z} {u : Z → Heights n} {g : Z → Joint n} {f : Joint n} {a : ℂ}
    (hu : ∀ᶠ t in l, u t ∈ east n) (hg : Tendsto g l (𝓝 f))
    (ht : Tendsto (fun t => F.psi v (u t) f) l (𝓝 a)) :
    Tendsto (fun t => F.psi v (u t) (g t)) l (𝓝 a) := by
  obtain ⟨m,C,_,hc⟩ := hp n v
  obtain ⟨h0,hcont⟩ := Waves.tolls (n := n) m C
  have htoll : Tendsto (fun t => Waves.toll (g t - f) C m) l (𝓝 0) := by
    rw [← h0]
    apply (hcont.tendsto 0).comp
    simpa using hg.sub (tendsto_const_nhds (x := f))
  have hh : Tendsto (fun t => F.psi v (u t) (g t - f)) l (𝓝 0) := by
    apply squeeze_zero_norm' ?_ htoll
    filter_upwards [hu] with t h
    rw [← F.meant ha hl _ _ h _ m]
    exact F.cost hc _ (bigger h) _
  rw [← zero_add a]
  apply (hh.add ht).congr'
  filter_upwards [hu] with t h
  change psiL F hb v (u t) h (g t - f) + F.psi .. = _
  rw [map_sub, show psiL F hb v (u t) h f = F.psi v (u t) f from rfl, sub_add_cancel]; rfl

lemma ray_mem {y : Heights n} (hy : y ∈ east n) {s : ℝ} (hs : 0 < s) : s • y ∈ east n :=
  fun _ _ hab => mul_lt_mul_of_pos_left (hy hab) hs

lemma hasDerivAt_zero_psi (hb : F.Bounds) (ha : F.Along) (hl : F.Lines) (hp : F.Breathes)
    (v : Fin n → X.W) (y : Heights n) (hy : y ∈ east n) (f : ℝ → Joint n) (s : ℝ) (hs : 0 < s)
    (hd : Tendsto (slope f s) (𝓝[≠] s) (𝓝 (- Boundary.Waves.clock y (f s)))) :
    HasDerivAt (fun t : ℝ => F.psi v (t • y) (f t)) 0 s := by
  have lines (g : Joint n) : HasDerivAt (fun t : ℝ => F.psi v (t • y) g)
      (F.psi v (s • y) (Boundary.Waves.clock y g)) s := by
    simpa using hl n v g 0 y s (by simpa using ray_mem hy hs)
  have hu : ∀ᶠ t in 𝓝[≠] s, t • y ∈ east n := (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hs)).mono
    (fun _ h => ray_mem hy h)
  have H := tendsto_psi F hb ha hl hp hu hd ((lines (- Boundary.Waves.clock y (f s))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [show F.psi v (s • y) (- Boundary.Waves.clock y (f s)) = -(F.psi v (s • y) (Boundary.Waves.clock y (f s))) from
    map_neg (psiL F hb v _ (ray_mem hy hs)) _] at H
  rw [hasDerivAt_iff_tendsto_slope, ← neg_add_cancel (F.psi v (s • y) (Boundary.Waves.clock y (f s)))]
  apply (H.add (lines (f s)).tendsto_slope).congr'
  filter_upwards [hu] with t ht
  simp only [slope_def_module]
  change psiL F hb v _ ht _ + _ = _
  rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
  change (t-s)⁻¹ • F.psi v _ _ - (t-s)⁻¹ • F.psi v _ _ + (_ - _) = _
  abel

/-- Absolute-coordinate strict height Fourier transform tested with compact
support after exponential multiplication; the original surface is kept. -/
lemma solar (W : Surface X) (hp:F.Breathes) (hv:F.Region S) (hw:F.NonTangentialFree W) : F.during W:=by
  have hl:=Waves.lines hv hp; have ha:=Waves.along hv hp
  intro n v y hy f hf
  let d := dawn y
  let K (t : ℝ) : Joint n := lifts (t • d) f hf
  let k := fun t => Probe.hat (K t)
  have hk (s : ℝ) : Tendsto (slope k s) (𝓝[≠] s) (𝓝 (-Boundary.Waves.clock y (k s))) := by
    have he := tendsto_exp_slope d f hf K (by intro t x; simp [K, real_inner_smul_left]) s
    rw [clock_hat, neg_neg]
    apply (Probe.hat.continuous.continuousAt.tendsto.comp he).congr'
    exact Eventually.of_forall fun t => ((Probe.hat.restrictScalars ℝ).toLinearMap.slope_comp K s t).symm
  have hd s (hs : 0 < s) := hasDerivAt_zero_psi F hw.int ha hl hp v y hy k s hs (hk s)
  let A (s : ℝ) := F.psi v (s • y) (k s)
  have const t (ht : 0 < t) : A t = A 1 := by
    refine (convex_Ioi (𝕜 := ℝ) (0:ℝ)).is_const_of_fderivWithin_eq_zero
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt) (fun s hs => ?_) ht (show (0:ℝ)<1 from zero_lt_one)
    rw [fderivWithin_of_isOpen isOpen_Ioi hs, (hd s hs).hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_zero]
  have h0 : k 0 = Probe.hat f := by
    change Probe.hat (lifts _ f hf) = _
    congr 1; ext1 x; simp
  have hlim : Tendsto A (𝓝[>] 0) (𝓝 (W.W n v (k 0))) :=
    tendsto_psi F hw.int ha hl hp (Eventually.mono self_mem_nhdsWithin (fun t ht => ray_mem hy (show 0<t from ht)))
      (((continuous_of_tendsto_slope _ _ hk).tendsto 0).mono_left nhdsWithin_le_nhds) ((hw.corner n v (k 0)).comp (show Tendsto (fun t:ℝ=> t • y) (𝓝[>] 0) (𝓝[east n] 0) from by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · simpa using ((tendsto_id (x:=𝓝 (0:ℝ))).smul (tendsto_const_nhds (x:=y))).mono_left (nhdsWithin_le_nhds (s:=Ioi 0))
        exact Eventually.mono self_mem_nhdsWithin (fun t ht=> ray_mem hy (show 0<t from ht))))
  rw [h0] at hlim
  have hu : Tendsto A (𝓝[>] 0) (𝓝 (A 1)) := tendsto_const_nhds.congr'
    (Eventually.mono self_mem_nhdsWithin (fun t ht => (const t (show 0<t from ht)).symm))
  simpa [A, k, K] using tendsto_nhds_unique hlim hu

private lemma support_lifts (u : Points n) (f : Joint n) (hf : HasCompactSupport ⇑f) :
    tsupport (lifts u f hf) ⊆ tsupport f :=
  tsupport_mul_subset_right

private lemma sunrise_smul {y : Heights n} (hy : y ∈ sunrise n) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ sunrise n := fun _ _ h => mul_le_mul_of_nonneg_left (hy h) ht

private lemma dawn_add (x y : Heights n) : dawn (x+y) = dawn x + dawn y := by
  ext1 i
  apply Mink.ext_by <;> simp [dawn, place]

private lemma dawn_smul (x : Heights n) (t : ℝ) : dawn (t • x) = t • dawn x := by
  ext1 i
  apply Mink.ext_by <;> simp [dawn, place]

variable (W : Surface X)

private lemma patch (hF : F.Breathes) (hp : F.during W)
    (v : Fin n → X.W) {y : Heights n} (hy : y ∈ sunrise n) :
    IsVanishingOn (Distn.fourier (W.W n v)) {x : Points n | inner ℝ (dawn y) x < -1} := by
  rw [Distn.from_compact]; intro f hs hf
  let Y (t : ℝ) := t • y + (1 : ℝ) • rate n
  let z := (1 : ℝ) • rate n
  let l (t : ℝ) := lifts (dawn (Y t)) f hf
  have hu : Tendsto l atTop (𝓝 0) := by
    let g := lifts (dawn z) f hf
    have hg : HasCompactSupport ⇑g := remains ..
    have hx (x) (H : x ∈ tsupport g) : inner ℝ (dawn y) x ≤ -1 :=
      le_of_lt (hs (support_lifts (dawn z) f hf H))
    refine (lift_falls (dawn y) g hg hx).congr fun t => ?_
    ext1 x
    change lifts (t • dawn y) g hg x = lifts (dawn (t • y + z)) f hf x
    rw [dawn_add, dawn_smul]
    simp only [g, rises, inner_add_left, Complex.ofReal_add, Complex.exp_add, mul_assoc]
  obtain ⟨m, C, -, H⟩ := hF n v
  have hw : Tendsto (fun t => weight (Probe.hat (l t))) atTop (𝓝 0) := by
    let A : Joint n →L[ℂ] Joint n := Probe.hat
    have hv := (((weight_cont (n := n)).comp A.continuous).tendsto 0).comp hu
    simpa only [Function.comp_def, map_zero, feath] using hv
  have hle : ‖Distn.fourier (W.W n v) f‖ ≤ C * (0 : ℝ) := by
    apply ge_of_tendsto (hw.const_mul C)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have he := sunrise_smul hy ht
    have hy' : Y t ∈ east n := dawns he zero_lt_one
    rw [hp n v (Y t) hy' f hf]
    have h1 : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
    have h := F.beam m C H he (Probe.hat (l t)) h1
    simp only [one_pow, one_mul] at h
    exact h
  rw [mul_zero] at hle
  exact norm_le_zero_iff.mp hle

lemma burnt (W : Surface X) (hF : F.Breathes) (hp : F.during W) (n:ℕ)(v:Fin n→X.W): dsupport (Distn.fourier (W.W n v)) ⊆ half n :=by
  intro p hs
  apply mem_iInter.mpr
  rintro ⟨y, hy⟩
  change 0 ≤ inner ℝ (dawn y) p
  by_contra! hx
  let t := 2 / (-inner ℝ (dawn y) p)
  have ht : 0 < t := div_pos (by norm_num) (neg_pos.mpr hx)
  let s := {x : Points n | inner ℝ (dawn (t • y)) x < -1}
  have hh : IsOpen s := isOpen_lt (by fun_prop) continuous_const
  apply Set.disjoint_left.mp ((Distn.general_open _ hh).mp
    (patch F W hF hp v (sunrise_smul hy ht.le))) _ hs
  change inner ℝ (dawn (t • y)) p < -1
  rw [dawn_smul, real_inner_smul_left]
  have he : t * inner ℝ (dawn y) p = -2 := by
    dsimp only [t]
    field_simp [hx.ne]
  rw [he]
  norm_num

end Waves
namespace Surface
variable (E:X.System P) (H:Fields.Euclidean S) (K:WSpins X) (W:Surface X)
open Probe
def Cones {X:Fields} (W:Surface X):=∀ n(v:Fin n→X.W), dsupport (Distn.fourier (W.W n v))⊆ coneM n
include E H K
lemma tents (hw:F.Region S) (hc:F.NonTangentialFree W)(hg:F.Breathes) : W.Cones:=by
  intro n p; have hv:=Waves.burnt F W hg (F.solar W hg hw hc) n
  rw [coneM]; apply subset_iInter; intro i
  let A := togetherL (Lorentz.dual i) n
  apply (Distn.due (Distn.fourier (W.W n p)) (A⁻¹' half n) ((submissive n).preimage A.continuous)).2
  intro t ht
  let z := along A.symm t
  obtain ⟨b, hb⟩:= MassiveTwoEstimates.SpinGeometry.geometry.realTime i
  let q := fun j => K.spin b (p j)
  have hZ : tsupport z ⊆ (half n)ᶜ := by
    have he : tsupport z ⊆ A.symm ⁻¹' tsupport t := by
      refine closure_minimal ?_ ((isClosed_tsupport t).preimage A.symm.continuous)
      intro x hx; exact subset_tsupport _ hx
    intro x hx hI; apply ht (he hx)
    rw [Set.mem_preimage]; rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hp := (Distn.due (Distn.fourier (W.W n q)) (half n) (submissive n)).mp (hv q) z hZ
  have hr (f:Joint n) : W.W n q (Probe.along (togetherL i _).symm f) = W.W n p f:=by rw [←Work.C09.motion_push,← hb]; exact Rotate.every_motion E H K hw hc hg b p f
  change W.W n _ (hat _)=_; rw [← hr (Probe.hat t), ← turns]; exact hp
end Surface
end YM.Massive.Bridge
