import YM.MassiveBridge.Panel
import YM.Shift.Ridge

/-!
# Positive contour, analytic in ordered times with uniform power estimate

As in YM/Work/C03. The Euclidean identity is on *all* `F.W` including odd.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Set Filter Function
open Boundary hiding Surface Waves Fields Small
open Boundary.Small (logD lit interval down bufferF)
open OS (Cross)
open scoped Topology NNReal BigOperators
variable {X : Massive.Fields} {S : X.Kernel} {C : Chamber S timeAxis} {n : ℕ}
-- separate holomorphic region from boundary
structure Waves (X : Fields) where
  F (n : ℕ) : Times n → SpacePoints n → MultilinearMap ℂ (fun _ : Fin n => X.W) ℂ
namespace Waves
variable (F : Waves X)
def restricted (v : Fin n → X.W) (y : Heights n) (p : Points n) := F.F n (shift p y) (trace p) v
structure Region (S : X.Kernel) : Prop where
  together (n : ℕ) (v : Fin n → X.W) : ContinuousOn (fun p : Times n × SpacePoints n =>
    F.F n p.1 p.2 v) (strict n ×ˢ univ)
  hol (n : ℕ) (v : Fin n → X.W) (x : SpacePoints n) :
    DifferentiableOn ℂ (fun z => F.F n z x v) (strict n)
  roots (n : ℕ) (v : Fin n → X.W) (x : SpacePoints n) (y : Heights n) (hy : y ∈ east n) :
    F.F n (fun i => ↑(y i)*Complex.I) x v = S n (place x y) v
-- despite Lean implicit S, use below S arg explicit

def Breathes : Prop := ∀ n (v : Fin n → X.W), ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m
end Waves
namespace MatrixCap
variable (B : MatrixCap C) in
def Defined (F : Waves X) : Prop := ∀ n (z : Times n), z ∈ strict n → ∀ p, lit z p →
    ∀ x v, F.F n z x v=B.matrix p n z x v

lemma coe_logD {k : ℝ} (hk : k ∈ Ioc (0 : ℝ) 1) : (logD k : ℝ) = k/8 := by
  unfold logD
  rw [min_eq_left hk.2, Real.coe_toNNReal _ (by have := hk.1; positivity)]

lemma enough_logD {k : ℝ} (hk : k ∈ Ioc (0 : ℝ) 1) {y : Heights n} (hb : broad y k) :
    Boundary.Small.enough y (logD k) := by
  have he := coe_logD hk
  have hp := hk.1
  have hq := hk.2
  refine ⟨?_, ?_, fun i j hij => ?_⟩
  · change (0:ℝ) < ↑(logD k); linarith
  · change (logD k:ℝ) < 1; linarith
  · linarith [hb i j hij]

lemma exists_lit {z : Times n} (hz : z ∈ strict n) : ∃ p, lit z p := by
  let y (i : Fin n) := (z i).im
  have he : ∀ᶠ k : ℝ in 𝓝[>] 0, k ∈ Ioc (0:ℝ) 1 ∧ broad y k := by
    have hw : ∀ᶠ k : ℝ in 𝓝[>] 0, broad y k := by
      unfold broad
      simp only [eventually_all]
      intro i j hij
      exact ((gt_mem_nhds (sub_pos.mpr (hz hij) : (0:ℝ) < y j-y i)).filter_mono
        nhdsWithin_le_nhds).mono (fun k h => le_of_lt h)
    filter_upwards [hw, self_mem_nhdsWithin, (gt_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with k hb hk hl using ⟨⟨hk, le_of_lt hl⟩,hb⟩
  obtain ⟨k,hk,hb⟩ := he.exists
  exact ⟨logD k,enough_logD hk hb⟩

lemma eventually_lit {z : Times n} {p : ℝ≥0} (hp : lit z p) :
    ∀ᶠ w in 𝓝 z, lit w p := by
  have hw : ∀ᶠ w in 𝓝 z, ∀ i j : Fin n, i<j → 4*(p:ℝ)<(w j).im-(w i).im := by
    simp only [eventually_all]
    intro i j hij
    exact ((show Continuous (fun w : Times n => (w j).im-(w i).im) by fun_prop).tendsto z).eventually
      (lt_mem_nhds (hp.2.2 i j hij))
  exact hw.mono (fun w h => ⟨hp.1,hp.2.1,h⟩)

lemma lit_strict {z : Times n} {p : ℝ≥0} (hp : lit z p) : z ∈ strict n :=
  fun i j hij => sub_pos.mp (lt_of_le_of_lt (show (0:ℝ) ≤ 4*p by positivity) (hp.2.2 _ _ hij))

lemma tail_lit {z : Times (n+1)} {p : ℝ≥0} (hp : lit z p) : lit (Fin.tail z) p :=
  ⟨hp.1,hp.2.1,fun i j hij => hp.2.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩

lemma tail_ready {z : Times (n+1)} {p : ℝ≥0} (hp : lit z p) (i : Fin n) :
    ((p+p:ℝ≥0):ℝ) < (Fin.tail z i - z 0).im := by
  rw [Complex.sub_im, NNReal.coe_add]
  have he := hp.2.2 0 i.succ (Fin.succ_pos _)
  change _ < (z i.succ).im - _
  linarith [show (0:ℝ) ≤ (p:ℝ) from p.property]

variable (B : MatrixCap C)

/-- Insert one bar in front of a multilinear ket. -/
def attach (p : ℝ≥0) (M : MultilinearMap ℂ (fun _ : Fin n => X.W) C.H.space) :
    MultilinearMap ℂ (fun _ : Fin (n+1) => X.W) C.H.space := by
  let f : X.W →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => X.W) C.H.space := {
    toFun v := (B.bar p v).toLinearMap.compMultilinearMap M
    map_add' v w := by
      ext1 u; change B.bar p (v+w) (M u) = _+_; rw [map_add]; rfl
    map_smul' c v := by
      ext1 u; change B.bar p (c•v) (M u) = c • B.bar p v (M u); rw [map_smul]; rfl
  }
  exact LinearMap.uncurryLeft f

lemma attach_apply (p : ℝ≥0) (M : MultilinearMap ℂ (fun _ : Fin n => X.W) C.H.space)
    (v : Fin (n+1) → X.W) : attach B p M v = B.bar p (v 0) (M (Fin.tail v)) := rfl

lemma train_multi (p : ℝ≥0) (z : Times n) (x : SpacePoints n) (Z : ℂ) (R : Space3) :
    ∃ M : MultilinearMap ℂ (fun _ : Fin n => X.W) C.H.space, ∀ v, M v = B.trainB p n z x v Z R := by
  induction n generalizing Z R with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty ℂ _ C.omega,fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨M,hM⟩ := ih (Fin.tail z) (Fin.tail x) (z 0) (x 0)
    let P := rip (C:=C) (z 0-Z) (p+p) (x 0-R)
    exact ⟨P.toLinearMap.compMultilinearMap (attach B p M),fun v => by
      change P (attach B p M v) = _; rw [attach_apply,hM]; rfl⟩

lemma matrix_multi (p : ℝ≥0) (z : Times n) (x : SpacePoints n) :
    ∃ M : MultilinearMap ℂ (fun _ : Fin n => X.W) ℂ, ∀ v, M v = B.matrix p n z x v := by
  cases n with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty ℂ _ (inner ℂ C.omega C.omega),fun _ => rfl⟩
  | succ n =>
    obtain ⟨M,hM⟩ := train_multi B p (Fin.tail z) (Fin.tail x) (z 0) (x 0)
    exact ⟨(innerSL ℂ C.omega).toLinearMap.compMultilinearMap (attach B p M),fun v => by
      change inner ℂ C.omega (attach B p M v) = _; rw [attach_apply,hM]; rfl⟩

lemma continuous_buffer : Continuous bufferF := by
  apply Continuous.subtype_mk
  exact Mink.divide.symm.continuous.comp (continuous_id.prodMk (continuous_const (y:=(0:ℝ))))

lemma rip_cont {D : Type*} [TopologicalSpace D] {u : D} (s : ℝ≥0)
    {z : D → ℂ} {x : D → Space3} {f : D → C.H}
    (hs : (s:ℝ) < (z u).im) (hz : ContinuousAt z u) (hx : ContinuousAt x u) (hf : ContinuousAt f u) :
    ContinuousAt (fun t => rip (C:=C) (z t) s (x t) (f t)) u := by
  have hU := (C.flow.cont_cross (T:=C.H.space × Cross timeAxis) Prod.fst Prod.snd continuous_fst continuous_snd).continuousAt.comp
    (hf.prodMk (continuous_buffer.continuousAt.comp hx))
  have hF := (C.flow.localHeat _ ((down _ _).2 hs)).continuousAt
  have hI : ContinuousAt (fun t => Boundary.Small.interval (z t) s) u := by
    unfold Boundary.Small.interval; fun_prop
  have ha := (hF.comp (f:=fun t => Boundary.Small.interval (z t) s) hI).clm_apply hU
  exact ha

lemma train_cont {D : Type*} [TopologicalSpace D] {u : D} (p : ℝ≥0)
    (v : Fin n → X.W) (z : D → Times n) (x : D → SpacePoints n) (Z : D → ℂ) (X : D → Space3)
    (he : lit (z u) p) (ht : ∀ i, ((p+p:ℝ≥0):ℝ) < (z u i-Z u).im)
    (hz : ∀ i, ContinuousAt (fun t => z t i) u) (hx : ∀ i, ContinuousAt (fun t => x t i) u)
    (hZ : ContinuousAt Z u) (hX : ContinuousAt X u) :
    ContinuousAt (fun t => B.trainB p n (z t) (x t) v (Z t) (X t)) u := by
  induction n generalizing Z X with
  | zero => exact continuousAt_const
  | succ n ih =>
    have hc := ih (Fin.tail v) (fun t => Fin.tail (z t)) (fun t => Fin.tail (x t)) (fun t => z t 0) (fun t => x t 0)
      (tail_lit he) (tail_ready he) (fun i => hz i.succ) (fun i => hx i.succ) (hz 0) (hx 0)
    exact rip_cont (p+p) (ht 0) ((hz 0).sub hZ) ((hx 0).sub hX) ((B.bar p (v 0)).continuous.continuousAt.comp hc)

lemma matrix_cont (v : Fin n → X.W) {p : ℝ≥0} {u : Times n × SpacePoints n} (he : lit u.1 p) :
    ContinuousAt (fun t : Times n × SpacePoints n => B.matrix p n t.1 t.2 v) u := by
  cases n with
  | zero => exact continuousAt_const
  | succ n =>
    have hc := train_cont B p (Fin.tail v) (u:=u) (fun t => Fin.tail t.1) (fun t => Fin.tail t.2)
      (fun t => t.1 0) (fun t => t.2 0) (tail_lit he) (tail_ready he)
      (fun i => (continuous_apply i.succ |>.comp continuous_fst).continuousAt)
      (fun i => (continuous_apply i.succ |>.comp continuous_snd).continuousAt) (by fun_prop) (by fun_prop)
    exact (innerSL ℂ C.omega).continuous.continuousAt.comp ((B.bar p (v 0)).continuous.continuousAt.comp hc)

lemma rip_diff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] {u : D} (s : ℝ≥0) (x : Space3)
    {z : D → ℂ} {f : D → C.H} (hs : (s:ℝ) < (z u).im)
    (hz : DifferentiableAt ℂ z u) (hf : DifferentiableAt ℂ f u) :
    DifferentiableAt ℂ (fun t => rip (C:=C) (z t) s x (f t)) u := by
  have hU := (C.flow.U (bufferF x)).differentiableAt.comp u hf
  have hF := (C.flow.localHeat _ ((down _ _).2 hs)).differentiableAt
  have hI : DifferentiableAt ℂ (fun t => Boundary.Small.interval (z t) s) u := by
    unfold Boundary.Small.interval; fun_prop
  have ha := (hF.comp u hI).clm_apply hU
  exact ha

lemma train_diff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] {u : D} (p : ℝ≥0)
    (v : Fin n → X.W) (z : D → Times n) (x : SpacePoints n) (Z : D → ℂ) (X : Space3)
    (he : lit (z u) p) (ht : ∀ i, ((p+p:ℝ≥0):ℝ) < (z u i-Z u).im)
    (hz : ∀ i, DifferentiableAt ℂ (fun t => z t i) u) (hZ : DifferentiableAt ℂ Z u) :
    DifferentiableAt ℂ (fun t => B.trainB p n (z t) x v (Z t) X) u := by
  induction n generalizing Z X with
  | zero => exact differentiableAt_const _
  | succ n ih =>
    have hd := ih (Fin.tail v) (fun t => Fin.tail (z t)) (Fin.tail x) (fun t => z t 0) (x 0)
      (tail_lit he) (tail_ready he) (fun i => hz i.succ) (hz 0)
    exact rip_diff (p+p) (x 0-X) (ht 0) ((hz 0).sub hZ) ((B.bar p (v 0)).differentiableAt.comp u hd)

lemma matrix_diff (v : Fin n → X.W) (x : SpacePoints n) {p : ℝ≥0} {u : Times n} (he : lit u p) :
    DifferentiableAt ℂ (fun t => B.matrix p n t x v) u := by
  cases n with
  | zero => exact differentiableAt_const _
  | succ n =>
    have hd := train_diff B p (Fin.tail v) Fin.tail (Fin.tail x) (fun t : Times _ => t 0) (x 0)
      (tail_lit he) (tail_ready he) (fun i => by change DifferentiableAt ℂ (fun t : Times _ => t i.succ) _; fun_prop)
      (by fun_prop)
    exact (innerSL ℂ C.omega).differentiableAt.comp u ((B.bar p (v 0)).differentiableAt.comp u hd)

lemma norm_train (p : ℝ≥0) (v : Fin n → X.W) (z : Times n) (x : SpacePoints n) (Z : ℂ) (X : Space3)
    (he : lit z p) (ht : ∀ i, ((p+p:ℝ≥0):ℝ) < (z i-Z).im) :
    ‖B.trainB p n z x v Z X‖ ≤ (∏ i, ‖B.bar p (v i)‖) * ‖C.omega‖ := by
  induction n generalizing Z X with
  | zero => simp [trainB]
  | succ n ih =>
    have hn := ih (Fin.tail v) (Fin.tail z) (Fin.tail x) (z 0) (x 0) (tail_lit he) (tail_ready he)
    rw [Fin.prod_univ_succ,mul_assoc]
    exact (flanks _ _ _ _ (ht 0)).trans (((B.bar p (v 0)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))

lemma norm_matrix (p : ℝ≥0) (v : Fin n → X.W) (z : Times n) (x : SpacePoints n) (he : lit z p) :
    ‖B.matrix p n z x v‖ ≤ ‖C.omega‖ * ((∏ i, ‖B.bar p (v i)‖) * ‖C.omega‖) := by
  cases n with
  | zero => simpa [MatrixCap.matrix] using (norm_inner_le_norm C.omega C.omega (𝕜:=ℂ))
  | succ n =>
    have hn := norm_train B p (Fin.tail v) (Fin.tail z) (Fin.tail x) (z 0) (x 0) (tail_lit he) (tail_ready he)
    rw [Fin.prod_univ_succ,mul_assoc ‖B.bar p (v 0)‖]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (((B.bar p (v 0)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _))) (norm_nonneg C.omega))

lemma defined_power (hpowers : ∀ v, B.rated v) {F : Waves X} (hF : B.Defined F) : F.Breathes := by
  intro n v
  choose Q d hQ h using fun i => hpowers (v i)
  let P (i : Fin n) := Q i * 8^d i
  have hP i : 0 ≤ P i := by have := hQ i; unfold P; positivity
  have hn := Finset.prod_nonneg (s:=Finset.univ) (fun i _ => hP i)
  refine ⟨∑ i, d i, ‖C.omega‖ * ((∏ i, P i) * ‖C.omega‖), by positivity, fun y k hk hb x => ?_⟩
  let p := logD k
  have hp : Boundary.Small.enough y p := enough_logD hk hb
  have he : lit (shift x y) p := by simpa [lit,shift] using hp
  have hi i : ‖B.bar p (v i)‖ ≤ P i * k⁻¹^d i := by
    apply (h i p ⟨hp.1,hp.2.1⟩).trans_eq
    unfold p P; rw [coe_logD hk,inv_div,div_eq_mul_inv,mul_pow,mul_assoc]
  calc ‖F.restricted v y x‖ = ‖B.matrix p n (shift x y) (trace x) v‖ := by rw [Waves.restricted, hF n _ (lit_strict he) p he]
       _ ≤ ‖C.omega‖ * ((∏ i, ‖B.bar p (v i)‖) * ‖C.omega‖) := norm_matrix B p v _ _ he
       _ ≤ ‖C.omega‖ * ((∏ i, (P i * k⁻¹^d i)) * ‖C.omega‖) := by gcongr with i; exact hi i
       _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; ring

lemma defined_exists {A : Spread C} (hB : B.concretized A) : ∃ F : Waves X, B.Defined F := by
  classical
  let F : Waves X := {
    F n z x := if h : z ∈ strict n then (matrix_multi B (exists_lit h).choose z x).choose else 0
  }
  refine ⟨F, fun n z hz p hp x v => ?_⟩
  change (if h : z ∈ strict n then (matrix_multi B (exists_lit h).choose z x).choose else 0) v = _
  rw [dif_pos hz, (matrix_multi B _ z x).choose_spec]
  exact matrix_fixed hB x v _ p (exists_lit hz).choose_spec hp

lemma defined_region (E : Fields.Euclidean S) {A : Spread C} (hB : B.concretized A) {F : Waves X} (hF : B.Defined F) : F.Region S := by
  refine ⟨fun n v u hu => ?_,fun n v x u hu => ?_,fun n v x y hy => ?_⟩
  · obtain ⟨p,hp⟩ := exists_lit hu.1
    apply ContinuousAt.continuousWithinAt
    apply (matrix_cont B v hp).congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto u).eventually (eventually_lit hp)] with t ht using
      hF n _ (lit_strict ht) p ht t.2 v
  · obtain ⟨p,hp⟩ := exists_lit hu
    exact ((matrix_diff B v x hp).congr_of_eventuallyEq ((eventually_lit hp).mono (fun t ht =>
      hF n t (lit_strict ht) p ht x v))).differentiableWithinAt
  · let z (i : Fin n) := (y i:ℂ)*Complex.I
    have hi : (fun i => (z i).im)=y := by simp [z]
    have hz : z ∈ strict n := show (fun i => (z i).im) ∈ east n from hi.symm ▸ hy
    obtain ⟨p,hp⟩ := exists_lit hz
    rw [hF n z hz p hp]
    exact root E hB x y v hy (hi ▸ (show Boundary.Small.enough (fun i => (z i).im) p from hp))

end MatrixCap
end YM.Massive.Bridge
