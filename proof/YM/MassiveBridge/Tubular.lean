import YM.MassiveBridge.Rays
import YM.Work.C10
import YM.Work.C11
import YM.Work.C12
import YM.Work.C13
import YM.Work.C14
import YM.Work.C15
import YM.Work.C16
/-!
# Full-tube extension to prepare spacelike commutation and uniqueness

With `Blanket` from YM. As in Work.C13--16, keep exact boundary
values and cones with the absolute Fourier convention. Lorentz motion uses spin lift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter Analysis MeasureTheory Distribution
open Boundary hiding Fields Surface Waves
open Probe Mink Mink.Poincare
open Work.C13 (lens_eq lens_reserve interiorLens interiorLens_apply phase shiftDeriv hasFDerivAt_shift)
open Work.C14 (modulation_all modulation_integrable)
open Work.C15 (east_broad blanketed_eq lifts_cancel eq_of_tests)
open Work.C16 (rect_mem_tube dual_mem_coneM)
open Bid (rect)
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace
variable {n : ℕ} {Q : Sequence} {P:Calibration Q} {Sys:Fields} {S:Sys.Kernel}
variable {F:Waves Sys}
lemma income (n): Bid.Wide n:=Work.C10.answer n
def pad (n): Blanket n:=Classical.choice (Work.C11.answer n)
lemma bought (B:Blanket n): B.Modified:= Work.C12.answer n (income n) B

theorem restricted_bounded {F : Waves Sys} (p : F.Breathes) (v : Fin n → Sys.W)
    {y : Heights n} (hy : y ∈ east n) : ∃ K : ℝ, ∀ x, ‖F.restricted v y x‖ ≤ K := by
  obtain ⟨m,C,_,h⟩ := p n v
  obtain ⟨k,hk,hb⟩ := east_broad hy
  exact ⟨_,h y k hk hb⟩

/-- At fixed ordered heights the tested wave really defines a tempered distribution. -/
theorem psi_tempered {F : Waves Sys} (p : F.Breathes) (b : F.Bounds) (v : Fin n → Sys.W)
    {y : Heights n} (hy : y ∈ east n) : ∃ u : Distn (Points n), ∀ f : Joint n, u f = F.psi v y f := by
  obtain ⟨K,hK⟩ := restricted_bounded p v hy
  let u : Joint n →ₗ[ℂ] ℂ :=
    { toFun := F.psi v y
      map_add' := by
        intro f g
        unfold Waves.psi
        rw [← integral_add (b n v y hy f) (b n v y hy g)]
        apply integral_congr_ae; filter_upwards with x; simp [mul_add]
      map_smul' := by
        intro c f
        change (∫ x, F.restricted v y x * (c • f) x) = c * F.psi v y f
        rw [Waves.psi, ← integral_const_mul]; apply integral_congr_ae
        filter_upwards with x; simp; ring }
  have hu : Continuous u := sways (fun f => K * weight f)
    (weight_cont.const_mul K) (by simp) (fun f => compromise f _ _ hK)
  exact ⟨⟨u,hu⟩,fun _ => rfl⟩

/-- Fourier transform of the strict restriction, then back to absolute position variables. -/
theorem partialD_psi {W : Surface Sys} {B : Blanket n} {F : Waves Sys} (hb : B.Modified)
    (hw : W.Cones) (p : F.Breathes) (b : F.Bounds) (d : F.during W)
    (v : Fin n → Sys.W) {y : Heights n} (hy : y ∈ east n) (f : Joint n) :
    B.partialD (W.W n v) (dawn y) f = F.psi v y f := by
  obtain ⟨u,hu⟩ := psi_tempered p b v hy
  let w := (Distn.fourier (W.W n v)).comp (B.diffuser (dawn y))
  have he (g : Joint n) (hg : HasCompactSupport ⇑g) : w g = Distn.fourier u g := by
    change Distn.fourier (W.W n v) (B.diffuser (dawn y) g) = u (hat g)
    rw [blanketed_eq hb _ (hw n v) _ (warmer n (etched hy)) _ hg,
      d n v y hy _ (remains _ g hg), lifts_cancel, hu]
  have hEq : w = Distn.fourier u := by
    ext1 g
    exact tendsto_nhds_unique_of_eventuallyEq ((w.continuous.tendsto g).comp (persistent g))
      (((Distn.fourier u).continuous.tendsto g).comp (persistent g))
      (Eventually.of_forall fun k => he (cap k g) (finite_cap k))
  change Distn.inverse w f = _
  rw [hEq, Distn.one, hu]

namespace Surface
structure Aurora (W : Surface Sys) (D : ∀ i : ℕ, Blanket i) where
  lens (n : ℕ) (p : Full n) : Joint n
  shape (n : ℕ) (p : Full n) (h : p∈tube n) : ∀ x, lens n p x = (D n).lens p x

namespace Aurora
variable {W : Surface Sys} {D : ∀ i : ℕ, Blanket i} (X : Aurora W D)

def emit (v : Fin n → Sys.W) (p : Full n) := ((pref (Points n))⁻¹ : ℂ) * Distn.fourier (W.W n v) (X.lens n p)

structure FullBody (F : Waves Sys) : Prop where
  hol (n : ℕ) (v : Fin n → Sys.W) : AnalyticOnNhd ℂ (X.emit v) (tube n)
  builds (n : ℕ) (v : Fin n → Sys.W) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    (D n).partialD (W.W n v) y f= ∫ x,X.emit v (glow x y) * f x
  leaned (n : ℕ) (v : Fin n → Sys.W) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    Integrable (fun x => X.emit v (glow x y) * f x)
  pure (n : ℕ) (v : Fin n → Sys.W) (x : Points n) (y : Heights n) (hp : y∈east n) : X.emit v (glow x (dawn y)) = F.restricted v y x

lemma sees {F : Waves Sys} (h : X.FullBody F) (v : Fin n → Sys.W) (y : Points n) (p : y∈shores n) (hm : (D n).Modified) (f : Joint n) :
    Tendsto (fun z => ∫ x, X.emit v (glow x z)*f x) (𝓝[fields n] y) (𝓝 ((D n).partialD (W.W n v) y f)) :=
    (((D n).tends hm _ f y p).mono (warmer n)).congr' (Eventually.mono self_mem_nhdsWithin fun _ hz => h.builds n _ _ hz _)

lemma lower {F : Waves Sys} (h : X.FullBody F) (v : Fin n → Sys.W) (y : Heights n) (x : Points n) (hp : y∈east n) :
    W.W n v =0 → F.restricted v y x=0 := by
  intro ht
  rw [← h.pure n v x y hp,emit,Distn.fourier_at,ht]; simp

lemma hasFDerivAt_interior (X : W.Aurora D) (hw : Bid.Wide n) (p : Full n) (hp : p ∈ tube n) :
    HasFDerivAt (X.lens n) (shiftDeriv (phase n) (X.lens n p)) p := by
  apply hasFDerivAt_shift
  · rw [show (X.lens n p : Points n → ℂ) = (D n).lens p from funext (X.shape n p hp)]
    exact lens_reserve _ hw p hp
  · filter_upwards [(south n).mem_nhds hp] with q hq x
    have h : phase n q x = phase n (q-p) x + phase n p x := by simp
    rw [X.shape n q hq x, X.shape n p hp x, lens_eq, lens_eq, h, Complex.exp_add, mul_assoc]

lemma analytic_interior (X : W.Aurora D) (hw : Bid.Wide n) (v : Fin n → Sys.W) :
    AnalyticOnNhd ℂ (X.emit v) (tube n) := by
  intro p hp
  apply PolyDisc.finiteD
  filter_upwards [(south n).mem_nhds hp] with q hq
  let F := Distn.fourier (W.W n v)
  have h : HasFDerivAt (fun x => F (X.lens n x))
      (F.comp (shiftDeriv (phase n) (X.lens n q))) q := by
    rw [hasFDerivAt_iff_isLittleOTVS]
    have ht := F.isBigOTVS_comp.trans_isLittleOTVS
      ((hasFDerivAt_iff_isLittleOTVS).mp (hasFDerivAt_interior X hw q hq))
    simpa only [Function.comp_def, map_sub, ContinuousLinearMap.comp_apply] using ht
  exact h.differentiableAt.const_mul _

lemma emit_integral (Y : W.Aurora D) (n : ℕ) (v : Fin n → Sys.W)
    (y : Points n) (h : y ∈ fields n) (hm : (D n).Modified) (f : Joint n) :
    (D n).partialD (W.W n v) y f = (∫ x, Y.emit v (glow x y) * f x) ∧
    Integrable (fun x => Y.emit v (glow x y) * f x) := by
  let P (x : Points n) := Y.lens n (glow x y)
  let g := P 0
  let w := Distn.fourier (W.W n v)
  have hP (x b : Points n) : P x b = plane b x * (D n).attenuate y b := by
    have hy : glow x y ∈ tube n := by simpa only [tube, mem_preimage, im_glow] using h
    simp only [P, Y.shape n _ hy, Blanket.lens, re_glow, im_glow]
  have hg (b : Points n) : g b = (D n).attenuate y b := by simp only [g, hP, plane_zero, one_mul]
  have hL (x b : Points n) : P x b = plane b x * g b := by rw [hP, hg]
  have he (q : Probe (Points n)) : (D n).diffuser y q = sew g q := by
    ext1 x
    rw [Blanket.diffuser, SchwartzMap.smulLeftCLM_apply_apply (hm.actual y (warmer n h)),
      sews, hg]
    rfl
  refine ⟨?_, modulation_integrable g P hL w f⟩
  change w ((D n).diffuser y (port f)) = _
  rw [he]
  exact modulation_all g P hL w f


lemma supplies (hw : W.Cones) (hF:F.Region S) (hp:F.Breathes) (hc:F.NonTangentialFree W) : ∃ Y: W.Aurora D,Y.FullBody F :=by
  let Y : W.Aurora D:= {
    lens n := interiorLens (D n) (income n)
    shape n p hp := interiorLens_apply (D n) (income n) p hp }
  have hY(n:ℕ)(v: Fin n→ Sys.W): AnalyticOnNhd ℂ (Y.emit v) (tube n):= analytic_interior Y (income n) v
  refine ⟨Y,hY,fun n v y h f=> (emit_integral Y n v y h (bought _) f).1,fun n v y h f=> (emit_integral Y n v y h (bought _) f).2,fun n v x y hy => ?_⟩
  have hx : Continuous (fun x : Points n => glow x (dawn y)) :=
    (Boundary.home n).comp (continuous_id.prodMk continuous_const)
  have ht (x : Points n) : glow x (dawn y) ∈ tube n := by simpa [tube] using etched hy
  have hg : Continuous (fun x : Points n => Y.emit v (glow x (dawn y))) :=
    continuousOn_univ.mp ((hY n v).continuousOn.comp hx.continuousOn (fun x _ => ht x))
  apply congr_fun (eq_of_tests _ _ hg (Waves.continuous_point hF v hy) _) x
  intro f; rw [←(emit_integral Y n v (dawn y) (etched hy) (bought _) f).1]; exact partialD_psi (bought _) hw hp hc.int (F.solar W hp hF hc) v hy f
lemma lens_support  (W : Surface Sys)
    (D : ∀ i, Blanket i) (Y : W.Aurora D) {n : ℕ} (r : Lorentz)
    {x : Full n} (hx : x ∈ tube n) :
    tsupport (Y.lens n x - along (togetherL (Lorentz.dual r) n) (Y.lens n (rect r x))) ⊆
      (coneM n)ᶜ := by
  let A := togetherL (Lorentz.dual r) n
  let U := Y.lens n x - along A (Y.lens n (rect r x))
  change tsupport U ⊆ _
  intro p ht hp
  have hA : A p ∈ coneM n := dual_mem_coneM r hp
  let N := Metric.ball p 1 ∩ (A ⁻¹' Metric.ball (A p) 1)
  have ho : IsOpen N := Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous)
  have hn : p ∈ N := ⟨Metric.mem_ball_self zero_lt_one,
    show A p ∈ Metric.ball (A p) 1 from Metric.mem_ball_self zero_lt_one⟩
  have he : Disjoint N (Function.support U) := by
    refine Set.disjoint_left.mpr ?_
    rintro q ⟨hq, hQ⟩ h
    have hc : (D n).cut q = 1 := (D n).immediate q ⟨p, hp, hq⟩
    have hC : (D n).cut (A q) = 1 := (D n).immediate (A q) ⟨A p, hA, hQ⟩
    apply h
    change Y.lens n x q - (along A (Y.lens n (rect r x))) q = 0
    rw [along_at, Y.shape n x hx q, Y.shape n (rect r x) (rect_mem_tube r hx)]
    have phase : plane (A q) (togetherL r n (reality x)) = plane q (reality x) := by
      rw [plane_dot, plane_dot q]
      simp only [plane, A, Boundary.parr]
    simp only [Blanket.lens, Blanket.attenuate, rect, re_glow, im_glow, hc, hC,
      phase, show inner ℝ (togetherL r n (shade x)) (A q) = inner ℝ (shade x) q from
        Boundary.parr r (shade x) q, sub_self]
  exact Set.disjoint_left.1 (he.closure_right ho) hn ht

lemma realTurn (K : WSpins Sys) (Y: W.Aurora D) (hw : W.Cones) (hrot:∀ (r: RealSpin)(v:Fin n→ Sys.W)(x:Joint n), W.W n (K.spin r ∘ v) (Probe.along (togetherL r.coord _).symm x) = W.W n v x) (v:Fin n→Sys.W)(r:RealSpin) (x: Full n)(hx:x∈tube n): Y.emit v x=Y.emit (K.spin r ∘ v) (rect r.coord x):=by
  let A := togetherL (Lorentz.dual r.coord) n
  let v' := fun i : Fin n => K.spin r (v i)
  let f := Y.lens n (rect r.coord x)
  have he : Distn.fourier (W.W n v) (Y.lens n x) = Distn.fourier (W.W n v) (along A f) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact ((Distn.due _ _ (closedM n)).1 (hw n v)) _ (lens_support W D Y r.coord hx)
  have hv (z : Joint n) :
      Distn.fourier (W.W n v') (along A.symm z) = Distn.fourier (W.W n v) z := by
    simp only [Distn.fourier_at, A, Boundary.turns]
    exact hrot r v (hat z)
  unfold Aurora.emit
  rw [he, ← hv (along A f), Probe.along_inv]
  rfl

end Aurora
end Surface
end YM.Massive.Bridge
