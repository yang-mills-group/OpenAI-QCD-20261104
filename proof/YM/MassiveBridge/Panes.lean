import YM.MassiveBridge.Tubular
import YM.Work.C17
import YM.Work.C20
import YM.Work.C21
/-!
# Exchange in the spin representation above an unswapped equality in the Schwinger kernel

Allow *other field values after the adjacent transposition*, so the test also
handles homogeneous odd slots. Argument is analytic Pane and identity transfer
as in YM/Work/C17-21, YM.Shift.Exchange. Does not need vacuum uniqueness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.AlongEdge
open Function Set Filter Analysis MeasureTheory Distribution Mink Mink.Poincare Complex
open Boundary hiding Fields Surface Waves
open Boundary.Probe
open Bid (augment travelable rect)
open Metric
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace
variable {n : ℕ} {C : Sequence} {Cal: Calibration C} {Sys: Massive.Fields} {S: Sys.Kernel}
variable {Y : Waves Sys} {W : Surface Sys} {D : ∀ n, Blanket n}
open Surface
open NearPair (north tip plain cont_plain flipW)
variable (P:NearPair n)
structure Panes (X : Aurora W D) (v u : Fin n → Sys.W) (y : Heights n) where
  permitted : P.Fleck y
  original (x : Points n) : x∈P.gap→ Pane (X.emit v) (tube n) (glow x (dawn y))
  tilted (x : Points n) : x∈P.gap→ Pane ((X.emit u) ∘ P.name) (P.name ⁻¹' tube n) (glow x (dawn y))

variable {P} {y : Heights n} {X : Aurora W D} {v u : Fin n → Sys.W} (B : Panes P X v u y)
/-- On-Slice Taylor agreement; a substantive port; not implied by equality just at t=0 values! -/
def Panes.sameGround : Prop := ∀ x (h : x∈P.gap), (∀ i : Fin n, YM.time (x i)=0) →
    (B.original x h).extendF =ᶠ[𝓝 (glow x (dawn y))] (B.tilted x h).extendF

theorem Panes.reaches (hx : B.sameGround) (x : Points n) (p : x∈P.gap) :
    (B.original x p).extendF =ᶠ[𝓝 (glow x (dawn y))] (B.tilted x p).extendF := by
  have HH : Continuous (@NearPair.name _ P) := (home n).comp ((P.switch.continuous.comp (cont_Re n)).prodMk (P.switch.continuous.comp (cont_sh n)))
  let q (t : unitInterval) := glow (plain x t) (dawn y)
  let w i := B.original _ (P.north p i)
  let z i := B.tilted _ (P.north p i)
  have he := Pane.propagate (south n) ((south n).preimage HH) q ((home n).comp
    (((cont_plain x).comp continuous_subtype_val).prodMk continuous_const))
    (fun t => ⟨B.permitted.first _,B.permitted.second _⟩) w z 0 1
  have hy := he.1 (hx _ _ (by simp [plain]))
  change (B.original (plain x 1) _).extendF =ᶠ[𝓝 (glow (plain x 1) (dawn y))] (B.tilted (plain x 1) _).extendF at hy
  let R (v : P.gap) : Prop := (B.original v.val v.2).extendF =ᶠ[𝓝 (glow v.val (dawn y))] (B.tilted v.val v.2).extendF
  change R (⟨x,p⟩ : P.gap); change R ⟨plain x 1,P.north p 1⟩ at hy
  rwa [show (⟨plain x 1,P.north p 1⟩ : P.gap)=(⟨x,p⟩ : P.gap) from Subtype.ext (tip x)] at hy

/-- local realization from each pane (full argument). Both at original x,
after change of names in tilted contour including positions and tests. -/
structure Panes.Forms : Prop where
  body (x : Points n) (hx : x∈P.gap) : ∃ r>0, ∀ f : Joint n, HasCompactSupport ⇑f → tsupport f ⊆ ball x r →
    (D n).partialD (W.W n v) (dawn y) f= ∫ i, (B.original x hx).extendF (glow i (dawn y))*f i
  prime (x : Points n) (hx : x∈P.gap) : ∃ r>0, ∀ f : Joint n, HasCompactSupport ⇑f → tsupport f ⊆ ball x r →
    flipW ((D n).partialD (W.W n u) (P.switch (dawn y))) P f= ∫ i,(B.tilted x hx).extendF (glow i (dawn y))*f i

theorem Panes.forgets (hp : B.sameGround) (hx : B.Forms) : IsVanishingOn (fun i =>
    ((D n).partialD (W.W n v) (dawn y)-flipW ((D n).partialD (W.W n u) (P.switch (dawn y))) P) i) P.gap := by
  let Q := (D n).partialD (W.W n v) (dawn y)
  let R := flipW ((D n).partialD (W.W n u) (P.switch (dawn y))) P
  apply (Distn.general_open (Q-R) P.open_gap).2
  apply Set.disjoint_left.2
  intro x H hI
  obtain ⟨r,hr,hR⟩ := hx.body x H
  obtain ⟨s,hs,hS⟩ := hx.prime x H
  let g (i : Points n) := glow i (dawn y)
  have hv : Continuous g := (home n).comp (continuous_id.prodMk continuous_const)
  obtain ⟨k,hk,ht⟩ := Metric.mem_nhds_iff.mp ((hv.tendsto x).eventually (B.reaches hp x H))
  let t := min k (min r s)
  have he := (mem_dsupport_iff_not_isVanishingOn x).mp hI (ball x t) (mem_ball_self (lt_min hk (lt_min hr hs))) isOpen_ball
  apply he; apply (Distn.from_compact (Q-R)).2
  intro f hl hf; change Q f-R f=0; apply sub_eq_zero.2
  rw [show Q f= _ from hR f hf (hl.trans (ball_subset_ball ((min_le_right ..).trans (min_le_left r s)))),
    show R f= _ from hS f hf (hl.trans (ball_subset_ball ((min_le_right ..).trans (min_le_right r s))))]
  classical
  apply integral_congr_ae; filter_upwards with i
  by_cases h : f i=0
  · simp [h]
  rw [show (B.original x H).extendF (g i)= _ from ht (ball_subset_ball (min_le_left k (min r s)) (hl (subset_tsupport _ h)))]

theorem actor (X : Aurora W D) (v u : Fin n → Sys.W) (P : NearPair n) (p : (D n).Modified)
    (hc : ∀ u : Fin n → Sys.W, dsupport (Distn.fourier (W.W n u)) ⊆ coneM n)
    (h : ∃ y : ℕ → Heights n, Tendsto (dawn ∘ y) atTop (𝓝 0) ∧
      ∀ m : ℕ, ∃ B : Panes P X v u (y m), B.sameGround ∧ B.Forms) : IsVanishingOn (fun f =>
    (W.W n v - flipW (W.W n u) P) f) P.gap := by
  obtain ⟨y,hy,hh⟩ := h
  choose B hb hB using hh
  have he : Tendsto (dawn ∘ y) atTop (𝓝[shores n] 0) := tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall (fun i => (B i).permitted.here)⟩
  have ht : Tendsto (fun i => P.switch (dawn (y i))) atTop (𝓝[shores n] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun i => (B i).permitted.there)⟩
    simpa only [Function.comp_def,map_zero] using (P.switch.continuous.tendsto 0 |>.comp hy)
  intro f hf
  let t : Joint n := along (P.switch).toContinuousLinearEquiv f
  have ha := ((D n).tends p (W.W n v) f _ (flat _)).tendsto.comp he
  have hw := ((D n).tends p (W.W n u) t _ (flat _)).tendsto.comp ht
  change W.W n v f-W.W n _ _=0
  apply sub_eq_zero.2
  rw [(D n).flatD p (hc v)] at ha
  rw [(D n).flatD p (hc _)] at hw
  exact tendsto_nhds_unique_of_eventuallyEq ha hw (Eventually.of_forall (fun i =>
    sub_eq_zero.mp ((B i).forgets (hb i) (hB i) f hf)))

private lemma reality_add (x y : Full n) :
    reality (x + y) = reality x + reality y := by
  apply Points.flatten.injective
  ext i
  simp [reality]

private lemma shade_add (x y : Full n) :
    shade (x + y) = shade x + shade y := by
  apply Points.flatten.injective
  ext i
  simp [shade]

private lemma reality_smul (c : ℂ) (x : Full n) :
    reality (c • x) = c.re • reality x - c.im • shade x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma shade_smul (c : ℂ) (x : Full n) :
    shade (c • x) = c.re • shade x + c.im • reality x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma glow_ext {x y : Full n} (h : reality x = reality y)
    (k : shade x = shade y) : x = y :=
  (valley x).symm.trans (by rw [h, k, valley])

private def complexMap (A : Points n →ₗ[ℝ] Points n) : Full n →L[ℂ] Full n :=
  LinearMap.toContinuousLinearMap
    { toFun x := glow (A (reality x)) (A (shade x))
      map_add' x y := by
        apply glow_ext <;> simp [reality_add, shade_add]
      map_smul' c x := by
        apply glow_ext <;> simp [reality_smul, shade_smul] }

private def blocks (A : E4 →L[ℝ] E4) : Points n →ₗ[ℝ] Points n where
  toFun x := points fun i => A (x i)
  map_add' x y := PiLp.ext fun i => map_add A (x i) (y i)
  map_smul' c x := PiLp.ext fun i => map_smul A c (x i)

private lemma analytic_name (P : NearPair n) (x : Full n) :
    AnalyticAt ℂ P.name x :=
  (complexMap P.switch.toLinearEquiv.toLinearMap).analyticAt x

private lemma analytic_augment (e : Ray) (z : ℂ) (x : Full n) :
    AnalyticAt ℂ (augment e z) x := by
  let U : Full n →L[ℂ] Full n := ContinuousLinearMap.id ℂ _ +
    Complex.sinh z • complexMap (blocks e.crossT) +
    (Complex.cosh z - 1) • complexMap (blocks e.scalesT)
  have h : augment e z = ⇑U := rfl
  rw [h]
  exact U.analyticAt x

private lemma analytic_boost_path (e : Ray) (x : Full n) (z : ℂ) :
    AnalyticAt ℂ (fun w => augment e w x) z :=
  (analyticAt_const.add (Complex.analyticAt_sinh.smul analyticAt_const)).add
    ((Complex.analyticAt_cosh.sub analyticAt_const).smul analyticAt_const)

/- The change of names must intertwine the action also for the *tilted*
pane. We need this identity only at real rapidities. -/

private lemma augment_real (e : Ray) (t : ℝ) (x : Full n) :
    augment e (↑t) x = rect (e.boost t) x := by
  apply glow_ext
  · simp only [augment, reality_add, reality_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, rect, re_glow]
    ext1 i
    simp [Ray.shift]
  · simp only [augment, shade_add, shade_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, add_zero, rect, im_glow]
    ext1 i
    simp [Ray.shift]

private lemma name_rect (P : NearPair n) (A : Lorentz) (x : Full n) :
    P.name (rect A x) = rect A (P.name x) := by
  have h (u : Points n) :
      P.switch (togetherL A n u) = togetherL A n (P.switch u) := PiLp.ext fun _ => rfl
  simp only [NearPair.name, rect, re_glow, im_glow, h]

variable {X : W.Aurora D} {F : Waves Sys}

private def emitAt (X : W.Aurora D) (x : Full n) :
    MultilinearMap ℂ (fun _ : Fin n => Sys.W) ℂ :=
  let A : Distn (Points n) →ₗ[ℂ] ℂ :=
    { toFun u := ((pref (Points n))⁻¹ : ℂ) * Distn.fourier u (X.lens n x)
      map_add' u v := by simp [mul_add]
      map_smul' c u := by simp [mul_left_comm] }
  A.compMultilinearMap (W.W n)

/- Separate slot labels move holomorphically at a fixed finite degree.
Expand in that finite basis to keep `FullBody.hol`'s fixed-label
hypothesis. In particular no claim about a norm on `Union`. -/
private lemma emit_analytic (hX : X.FullBody F) (d : ℕ) [FiniteDimensional ℂ (Sys.level d)] (u : Fin n → ℂ → ↥(Sys.level d))
    (w : ℂ → Full n) (z : ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) z)
    (hw : AnalyticAt ℂ w z) (hin : w z ∈ tube n) :
    AnalyticAt ℂ (fun b => X.emit (fun i => (Sys.level d).subtype (u i b)) (w b)) z := by
  classical
  let B := Module.finBasis ℂ (↥(Sys.level d))
  have he : (fun b => X.emit (fun i => (Sys.level d).subtype (u i b)) (w b)) =
      fun b => ∑ j : Fin n → Fin (Module.finrank ℂ (↥(Sys.level d))),
        (∏ i, B.coord (j i) (u i b)) • X.emit (fun i => (Sys.level d).subtype (B (j i))) (w b) := by
    funext b
    have hp : (fun i => (Sys.level d).subtype (u i b)) =
        fun i => ∑ j, B.coord j (u i b) • (Sys.level d).subtype (B j) := by
      funext i
      conv_lhs => rw [← B.sum_repr (u i b), map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      rfl
    rw [hp]
    change emitAt X (w b) _ = _
    rw [MultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (emitAt X (w b)).map_smul_univ _ _
  rw [he]
  apply ContDiffAt.analyticAt
  refine ContDiffAt.sum (fun j hj => ?_)
  apply ContDiffAt.mul
  · refine contDiffAt_prod (fun i hi => ?_)
    let A : ↥(Sys.level d) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (B.coord (j i))
    exact ((A.analyticAt _).comp (hu i)).contDiffAt
  exact ((hX.hol n _ _ hin).comp hw).contDiffAt

/- An anchored germ, also applicable after a change of names `N`. Use
wave_turn for equality on the real boost line (only a neighborhood of zero
is needed), then uniqueness in a *single* complex parameter on the
preconnected path image. `AnalyticOnNhd` gives actual analyticity at each
point of the path, so that image needn't itself be open. -/
private lemma paneAlong (E : Sys.System Cal) {K: WSpins Sys} (hX : X.FullBody F)
    (hTurn : ∀ (v:Fin n→Sys.W)(r:RealSpin) x (_ : x ∈ tube n), X.emit v x=X.emit (K.spin r ∘ v) (rect r.coord x))
    (v : Fin n → Sys.W) (e : Ray)
    (N : Full n → Full n) (hN : AnalyticOnNhd ℂ N univ)
    (hReal : ∀ (a : ℝ) l, N (augment e (↑a) l) = rect (e.boost a) (N l))
    (γ : ℝ → ℂ) (hγ : Continuous γ) (h0 : γ 0 = 0) {x : Full n} {t : ℝ} (ht : 0 ≤ t)
    (hend : N (augment e (γ t) x) ∈ tube n)
    (hpath : ∀ᶠ l in 𝓝[N ⁻¹' tube n] x, ∀ b : ℝ, b ∈ Icc 0 t →
      N (augment e (γ b) l) ∈ tube n) :
    Nonempty (Pane (X.emit v ∘ N) (N ⁻¹' tube n) x) := by
  obtain ⟨d, a, rfl⟩ := Rotate.cover_cap E v
  haveI:= E.finite d
  choose U ha hr using fun i:Fin n=> K.entire e d (a i)
  let V (z : ℂ) (i : Fin n) := (Sys.level d).subtype (U i z)
  let Q (l : Full n) (z : ℂ) := X.emit (V z) (N (augment e z l))
  refine ⟨⟨fun l => Q l (γ t), ?_, ?_⟩⟩
  · exact (hX.hol n (V (γ t)) _ hend).comp (f := N ∘ augment e (γ t))
      ((hN _ (mem_univ _)).comp (f := augment e (γ t)) (analytic_augment e (γ t) x))
  filter_upwards [hpath, self_mem_nhdsWithin] with l hl hin
  let k := X.emit ((Sys.level d).subtype ∘ a) (N l)
  change Q l (γ t) = k
  have ha' : AnalyticOnNhd ℂ (Q l) (γ '' Icc 0 t) := by
    rintro z ⟨b, hb, rfl⟩
    refine emit_analytic hX d (fun i z => U i z)
      (fun z => N (augment e z l)) (γ b) (fun i => ?_) ?_ (hl b hb)
    · exact ((ha i).differentiableOn (s:=univ)).analyticOnNhd isOpen_univ _ (mem_univ _)

    exact (hN _ (mem_univ _)).comp (analytic_boost_path e l _)
  have he (r : ℝ) : Q l (↑r) = k := by
    have hV : V (↑r) = fun i => K.spin (MassiveTwoEstimates.BoostMotion.point e r) (((Sys.level d).subtype ∘ a) i) := by
      funext i
      exact hr i r
    change X.emit (V _) (N (augment e _ l)) = _
    rw [hV, hReal]
    exact (hTurn ((Sys.level d).subtype ∘ a) (MassiveTwoEstimates.BoostMotion.point e r) (N l) hin).symm
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Q l z = k := by
    have hu : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with r hr
      change (r : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (mem_Ioi.mp hr).ne'
    intro hx
    obtain ⟨r, hr⟩ := (hu.eventually hx).exists
    exact hr (he r)
  have hg : EqOn (Q l) (fun _ => k) (γ '' Icc 0 t) :=
    ha'.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      (isPreconnected_Icc.image γ hγ.continuousOn) ⟨0, left_mem_Icc.mpr ht, h0⟩ hfreq
  exact hg ⟨t, right_mem_Icc.mpr ht, rfl⟩

lemma answer (E:Sys.System Cal) (K:WSpins Sys) (hX:X.FullBody Y) (hTurn : ∀ (v:Fin n→Sys.W)(r:RealSpin) x (_ : x ∈ tube n), X.emit v x=X.emit (K.spin r ∘ v) (rect r.coord x)) (v u: Fin n→ Sys.W) (Z : NearPair n) (y : Heights n) (hy: Z.Fleck y) (ht:∀ x∈ Z.gap,∃ e t, travelable e Z t (glow x (dawn y))) : Nonempty (Panes Z X v u y):=by
  have hg (x : Points n) (hx : x ∈ Z.gap) :
      Nonempty (Pane (X.emit v) (tube n) (glow x (dawn y))) ∧
      Nonempty (Pane ((X.emit u) ∘ Z.name) (Z.name ⁻¹' tube n) (glow x (dawn y))) := by
    obtain ⟨e, t, hp, ho, hs, hpos, hneg⟩ := ht x hx
    constructor
    · exact paneAlong E hX hTurn v e id (fun _ _ => analyticAt_id)
        (augment_real e) (fun b => (b : ℂ)*I) (by fun_prop) (by simp) hp.le ho hpos
    exact paneAlong E hX hTurn u e Z.name (fun x _ => analytic_name Z x)
      (fun b l => by rw [augment_real, name_rect]) (fun b => -(b : ℂ)*I)
      (by fun_prop) (by simp) hp.le hs hneg
  exact ⟨⟨hy, fun x hx => Classical.choice (hg x hx).1,
    fun x hx => Classical.choice (hg x hx).2⟩⟩


open Work.C20 hiding answer
variable {X₀ : W.Aurora D} (Vt: NearPair n) (b v : Fin n→Sys.W)
private lemma emit_s (ht:Y.Region S)(hp:X₀.FullBody Y)(w:Fin n→Sys.W){q:Points n}(h:q∈Work.C20.ordered n): X₀.emit w (wickSlice n q)=S n q w:=by
    let t := Boundary.trace q
    have hy : readings q∈east n:=h
    have hspace: Boundary.trace (place t 0)=t:=by funext i; simp [Boundary.trace,place,t]
    have htime: shift (place t 0) (readings q)=(fun i=> (time (q i):ℂ)*I):=by funext i; simp [shift,readings,place]
    rw [wick_glow,hp.pure n w _ _ hy,Waves.restricted,htime,hspace]
    exact (ht.roots n w t _ hy).trans (by rw [show place t (readings q)=q from place_same q])

lemma sameGround {X: NearPair n} {y : Heights n} (hs:Fields.Euclidean S) (hR:Y.Region S)(hF:X₀.FullBody Y)(h:∀ (x : Points n),x∈conf n → S _ (X.switch x) b=S _ x v)(A: Panes X X₀ v b y): A.sameGround:=by
  let Z:=X₀
  intro x hx hz
  let p := place (Boundary.trace x) y
  let M := wickSlice n
  let f := (A.original x hx).extendF
  let g := (A.tilted x hx).extendF
  have hy : X.spectator y := A.permitted.willing
  have hup : readings p = y := readings_place ..
  have hvp : readings (X.switch p) = y := same_height hy.1 _
  have hp := euclid_conf hy hx
  have hspace : Boundary.trace p = Boundary.trace x := by funext i; simp [Boundary.trace, p, place]
  have hx0 : readings x = 0 := funext hz
  have hM : M p = glow x (dawn y) := by
    unfold M
    rw [wick_glow, hup, hspace, ← hx0, place_same]
  change f =ᶠ[𝓝 _] g
  have ha : AnalyticAt ℂ f (M p) := hM.symm ▸ (A.original x hx).doc
  have hb : AnalyticAt ℂ g (M p) := hM.symm ▸ (A.tilted x hx).doc

  let C := fun x => S _ x v
  have hC : ContDiffAt ℝ ∞ C p:= (hs.smooth n v p hp).contDiffAt ((conf_open n).mem_nhds hp)

  have hu : Tendsto M (𝓝[ordered n] p) (𝓝[tube n] (glow x (dawn y))) := by
    rw [← hM]
    exact M.continuous.continuousWithinAt.tendsto_nhdsWithin wick_tube
  have heq : f ∘ M =ᶠ[𝓝[ordered n] p] C := by
    have hf : f ∘ M =ᶠ[𝓝[ordered n] p] Z.emit v ∘ M := hu.eventually (A.original x hx |>.fits)
    refine hf.trans ?_
    filter_upwards [self_mem_nhdsWithin] with i hi using emit_s hR hF v hi

  let V : Set (Points n) := X.switch ⁻¹' ordered n
  have hu' : Tendsto M (𝓝[V] p) (𝓝[X.name ⁻¹' tube n] (glow x (dawn y))) := by
    rw [← hM]
    refine M.continuous.continuousWithinAt.tendsto_nhdsWithin fun u hu => ?_
    change X.name (wickSlice n u) ∈ tube n
    rw [wick_name]; exact wick_tube (show X.switch u ∈ ordered n from hu)
  have heq' : g ∘ M =ᶠ[𝓝[V] p] C := by
    have hg : g ∘ M =ᶠ[𝓝[V] p] ((Z.emit b) ∘ X.name) ∘ M :=
      hu'.eventually (A.tilted x hx |>.fits)
    refine hg.trans ?_
    have hn : ∀ᶠ u in 𝓝[V] p, u ∈ conf n :=
      Eventually.filter_mono nhdsWithin_le_nhds ((conf_open n).mem_nhds hp)
    filter_upwards [self_mem_nhdsWithin, hn] with u hu hc
    simp only [Function.comp_apply, M, wick_name]
    exact (emit_s hR hF b (show X.switch u ∈ ordered n from hu)).trans
      (h u hc)

  rw [← hM]
  refine complex_germ ha hb (wick_span n) fun m => ?_
  have hm : ContDiffAt ℝ m C p := hC.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf : ContDiffAt ℂ m f (M p) := ha.contDiffAt
  have hg : ContDiffAt ℂ m g (M p) := hb.contDiffAt
  have hne := ordered_neBot (q := p) (hup.symm ▸ before_east hy)
  have hne' := switch_neBot X (q := p) (hvp.symm ▸ before_east hy)
  exact (jets_on_open_side (ordered_open n) hne heq m ((hf.restrict_scalars ℝ).comp p M.contDiff.contDiffAt)
    hm).trans (jets_on_open_side ((ordered_open n).preimage X.switch.continuous) hne' heq'.symm m
      hm ((hg.restrict_scalars ℝ).comp p M.contDiff.contDiffAt))


lemma forms {Z:W.Aurora D} (hF: Z.FullBody Y) {v b: Fin n→Sys.W}{Zp:NearPair n}{y:Heights n}(A:Panes Zp Z v b y): A.Forms:=by
  constructor
  · intro x hx
    refine Work.C21.realize (V := fields n) (fun _ => Iff.rfl) (A.permitted.first x) (A.original x hx) (fun z hz => ?_)
      (Z.sees hF v _ A.permitted.here (bought _))
    exact (hF.hol n v).continuousOn.comp_continuous ((home n).comp (continuous_id.prodMk continuous_const))
      (fun _ => show shade (glow _ z) ∈ fields n by simpa using hz)
  intro x hx
  let V := Zp.switch ⁻¹' fields n
  have hV p : p ∈ Zp.name ⁻¹' tube n ↔ shade p ∈ V := by
    change shade (Zp.name p) ∈ fields n ↔ Zp.switch (shade p) ∈ fields n
    simp [NearPair.name]
  refine Work.C21.realize hV (A.permitted.second x) (A.tilted x hx) (fun z hz => ?_) (fun f => ?_)
  · have he : Continuous Zp.name := (home n).comp ((Zp.switch.continuous.comp (cont_Re n)).prodMk
      (Zp.switch.continuous.comp (cont_sh n)))
    exact (hF.hol n _).continuousOn.comp_continuous (he.comp ((home n).comp (continuous_id.prodMk continuous_const)))
      (fun _ => (hV _).2 (show shade (glow _ z) ∈ V by simpa using hz))
  have ht := Z.sees hF b _ A.permitted.there (bought _) (along Zp.switch.toContinuousLinearEquiv f)
  have hP : Tendsto Zp.switch (𝓝[V] dawn y) (𝓝[fields n] Zp.switch (dawn y)) :=
    Zp.switch.continuous.continuousWithinAt.tendsto_nhdsWithin fun _ h => h
  exact (ht.comp hP).congr' (Eventually.of_forall (Work.C21.reindex (Z.emit b) Zp f))

lemma exchange (E:Sys.System Cal)(Hs:Fields.Euclidean S)(K:WSpins Sys)(he:Y.Region S) (hw : Y.NonTangentialFree W) (hp : Y.Breathes)
    (Z: W.Aurora D)(HZ:Z.FullBody Y) (P : NearPair n) (v b: Fin n→Sys.W) (h:∀ (x:Points n), x∈conf _ → S _ (P.switch x) b=S _ x v) (f : Joint n)(hf: tsupport f ⊆ P.gap): W.W n v f = W.W n b (along P.switch.toContinuousLinearEquiv f):=by
   obtain ⟨y,hy,ht⟩:=Work.C17.answer n P
   have hc:= Surface.tents Y E Hs K W he hw hp
   apply sub_eq_zero.mp (actor Z v b P (bought _) (hc n) (Exists.intro y ⟨hy,?_⟩) f hf : W.W n v f- W.W n b (along P.switch.toContinuousLinearEquiv f)=0)
   intro m
   have hr :∀ (r: RealSpin)(v:Fin n→ Sys.W)(x:Joint n), W.W n (K.spin r ∘ v) (Probe.along (togetherL r.coord _).symm x) = W.W n v x:=by
      intro r v x; rw [←Work.C09.motion_push]; exact Rotate.every_motion E Hs K he hw hp r v x
   obtain ⟨A⟩:= answer E K HZ (Aurora.realTurn K Z hc hr) v b P _ (ht m).1 (ht m).2
   exact ⟨A,sameGround b v Hs he HZ h A,forms HZ A⟩
end YM.Massive.Bridge.AlongEdge
