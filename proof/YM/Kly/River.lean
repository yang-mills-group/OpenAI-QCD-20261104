import YM.MassiveBridge.Inserts
import YM.Ground.Lean
import YM.MassiveTwoEstimates.SpinGeometry
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Filter Set Analysis
open Fields (pointMoment distinct)
open OS (Cross)
open scoped ContDiff Topology BigOperators InnerProductSpace NNReal ComplexOrder
variable {F:Fields}{a:Axis}{S: F.Kernel}(V:Chamber S a)(hJ:Involutive (F.adj a))
lemma happens (d : ℝ≥0 → E4) (H : Tendsto (fun i => d i a) atTop atTop) (p v : Cluster F) (hp : distinct p)
    (hv : distinct v) : ∀ᶠ i in atTop, distinct (p ++ carry v (d i)) := by
  classical
  have hk (q u : Plant F) : ∀ᶠ i in atTop, q.1 a < (u.1+d i) a := by
    filter_upwards [H.eventually (eventually_gt_atTop (q.1 a - u.1 a))] with i hi; simp only [PiLp.add_apply]; linarith
  filter_upwards [(eventually_all_finset p.toFinset).mpr fun i (_:i∈_) => (eventually_all_finset v.toFinset).mpr fun j (_:j∈_) => hk i j] with i hi
  apply locations.mpr; rw [List.map_append,List.nodup_append]; refine ⟨locations.mp hp, locations.mp (still hv _),?_⟩
  intro x hx y hy he
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
  exact (hi q (by simpa using hq) u (by simpa using hu)).ne (congr_arg (fun z : E4 => z a) he)

def rotate (w:Cluster F)(K:EuPin):Cluster F := w.map fun p => (Ortho.move K.coord p.1,F.action K p.2)
lemma rotated (w v:Cluster F) (K:EuPin)(b:E4): rotate (w++carry v b) K=rotate w K++carry (rotate v K) (Ortho.move K.coord b):=by
    unfold rotate; simp only[carry,List.map_append,List.map_map]; congr 2; funext p; exact Prod.ext ((Ortho.motion _).map_add _ _) rfl
abbrev Angular (S:F.Kernel):Prop:=∀ (p:EuPin)(w:Cluster F), distinct w → pointMoment S (rotate w p)=pointMoment S w
variable (HA:Angular S)
lemma trans {w:Cluster F} (Y:Angular S) (hX:distinct w) (K:EuPin):distinct (rotate w K)∧pointMoment S (rotate w K)=pointMoment S w:=by
     refine ⟨?_, Y K w hX⟩; rw [locations,show (rotate w K).map Prod.fst=(w.map Prod.fst).map (Ortho.move K.coord) from by simp only[rotate,List.map_map]; rfl]; exact (locations.mp hX).map (Ortho.move_injective _)
lemma going (_ : Fields.Euclidean S) (p q : Future F a) (x : Cross a) (s : ℝ≥0) : inner ℂ (V.GNS.plant p)
    (V.flow.U x (V.flow.E s (V.GNS.plant q))) = pointMoment S (reflect p.val a ++ carry q.val (x.val + (s:ℝ) • basis a)) := by
  rw [← V.atBirth, ← V.across, V.GNS.measure]; simp [kernel,travel, over, add_comm]

-- choose lower/upper placements fixed. p sent to reflection of word.
lemma released (p : Cluster F) (h : distinct p) : ∃ r : ℝ, Positive (carry p (r • basis a)) a := by
  classical
  have ht i (hi : i∈p) : ∀ᶠ r : ℝ in atTop, 0 < i.1 a+r := by
    filter_upwards [eventually_gt_atTop (-i.1 a)] with t ht; linarith
  obtain ⟨r,hr⟩ := ((eventually_all_finset p.toFinset).mpr (fun i hi => ht i (by simpa using hi))).exists
  refine ⟨r,still h _,fun i hp => ?_⟩
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hp
  simpa using hr _ (by simpa using hu)

include hJ
lemma settles (p q : Cluster F) (h : distinct p) (hp : distinct q) (H : Fields.Euclidean S) :
    ∃ (t s : ℝ) (v w : Future F a), ∀ (x : E4) (_ : t+s ≤ x a),
      pointMoment S (p++carry q x) = inner ℂ (V.GNS.plant v) (V.flow.U (OS.Semigroup.SEP a x) (V.flow.E (x a-t-s).toNNReal (V.GNS.plant w))) := by
  obtain ⟨t,hv⟩ := released (reflect p a) (reflects a h) (a := a)
  obtain ⟨s,he⟩ := released q hp (a := a)
  let v := (⟨_,hv⟩ : Future F a)
  let w := (⟨_,he⟩ : Future F a)
  refine ⟨t,s,v,w,fun x ht => ?_⟩
  let f := OS.Semigroup.SEP a x
  let k := (x a-t-s).toNNReal
  have hw := twoSides v.property (over (travel w k) f).property
  have hy : (over (travel w k) f).val=carry w.val (f.val+(k:ℝ) • basis a) := by simp [over,travel,add_comm]
  have hh : carry (reflect v.val a ++ carry w.val (f.val+(k:ℝ) • basis a)) (t • basis a)=p ++ carry q x := by
    dsimp only [v,w]; rw [refl_over,reflect_twice _ hJ,distribute,paths,paths,paths,
      show Ortho.move (Signed.reflect a) (t • basis a) = -(t • basis a) by ext i; by_cases h : i=a <;> simp [h,Signed.mirrored], neg_add_cancel, rest]
    congr 2
    change _+(((x-x a • basis a)+ (k:ℝ) • _)+ _)=x
    dsimp only [k]; rw [Real.coe_toNNReal _ (by linarith)]; module
  rw [going V H, ← hh]
  exact invariance H (hy ▸ hw) _

def ing (S:F.Kernel) (p q : Cluster F) (x : E4) := pointMoment S (p++carry q x)
include V hJ
lemma overtops (H : Fields.Euclidean S) (d : ℝ≥0 → E4) (h : Tendsto (fun x => d x a) atTop atTop) (p q : Cluster F)
    (hp : distinct p) (hq : distinct q) (u : ℝ) :
    Tendsto (fun i => ing S p q (d i+u • basis a)-ing S p q (d i)) atTop (𝓝 0) := by
  obtain ⟨r,s,v,w,H⟩ := settles V hJ p q hp hq H
  let u' := fun i : ℝ≥0 => d i+u • basis a
  have he : Tendsto (fun i => u' i a) atTop atTop := by simp [u']; exact tendsto_atTop_add_const_right atTop _ h
  let t (f : ℝ≥0 → E4) (i) := (f i a-r-s).toNNReal
  have hx (f : ℝ≥0 → E4) (hh : Tendsto (fun i => f i a) atTop atTop) : Tendsto (t f) atTop atTop := by
    refine Real.tendsto_toNNReal_atTop.comp ?_
    simp_rw [sub_eq_add_neg]
    apply tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ hh)
  let V' := V.GNS.plant v
  let Y := OS.Semigroup.SEP a
  let D (i) := V.flow.E (t u' i) (V.GNS.plant w) -V.flow.E (t d i) (V.GNS.plant w)
  have ht := V.flow.emerges (V.GNS.plant w)
  have hw : Tendsto D atTop (𝓝 0) := by simpa only [sub_self,Function.comp_apply,D] using (ht.comp (hx u' he)).sub (ht.comp (hx d h))
  have hz : Tendsto (fun i => V.flow.U (Y (d i)) (D i)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; simp_rw [V.flow.unitary]; simpa using hw.norm
  have hn : Tendsto (fun i => inner ℂ V' (V.flow.U (Y (d i)) (D i))) atTop (𝓝 0) := by
    simpa only [inner_zero_right] using (tendsto_const_nhds (x := V')).inner hz (𝕜 := ℂ)
  apply hn.congr'
  filter_upwards [h.eventually (eventually_ge_atTop (r+s)),he.eventually (eventually_ge_atTop (r+s))] with i hi hp
  rw [ing,ing,H _ hp,H _ hi,show Y (u' i)=Y (d i) from by
    dsimp only [u']; rw [map_add, show Y (u • basis a)=0 from Subtype.ext (show (u • basis a -_ : E4)=0 by simp),add_zero]] -- zeta
  unfold D; rw [map_sub,inner_sub_right]

lemma across_axis (H : Fields.Euclidean S) (R : Angular S) (w : E4) (hw : 0 < w a) (p q : Cluster F)
    (hp : distinct p) (hq : distinct q) : Tendsto (fun i : ℝ≥0 => ing S p q (w+(i:ℝ) • basis a)-ing S p q ((i:ℝ) • basis a)) atTop (𝓝 0) := by
  obtain ⟨K,hK,hc⟩:= OS.Ground.orients w hw; obtain ⟨K,rfl⟩:= MassiveTwoEstimates.SpinGeometry.geometry.euclidean K
  have ht : Tendsto (fun i : ℝ≥0 => (i:ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  let f (i : ℝ≥0) := (i:ℝ) • basis a
  have hf : Tendsto (fun i => f i a) atTop atTop := by simpa only [f,PiLp.smul_apply,basis_eq, if_true,smul_eq_mul,mul_one] using ht
  have hy (x : E4) (hh : distinct (p++carry q x)) :
      ing S (rotate p K) (rotate q K) (Ortho.move K.coord x)=ing S p q x := by
    unfold ing; rw [← rotated]; exact (trans R hh K).2
  have hZ := overtops V hJ H (fun i => Ortho.move K.coord (f i)) ?_ (rotate p K) (rotate q K) (trans R hp K).1 (trans R hq K).1 ‖w‖
  · apply hZ.congr'
    filter_upwards [happens f hf p q hp hq, happens (fun i => w+f i)
      (a := a) (show Tendsto (fun i => (w+f i) a) _ _ from tendsto_atTop_add_const_left _ _ hf) p q hp hq] with i hi hh
    rw [hy _ hi, add_comm (Ortho.move _ _),← hK,← show Ortho.move K.coord (w+f i)= Ortho.move K.coord w+Ortho.move K.coord (f i) from (Ortho.motion K.coord).map_add w (f i), hy _ hh]
  have he i : Ortho.move K.coord (f i)=(i:ℝ) • Ortho.move K.coord (basis a) := (Ortho.motion K.coord).map_smul _ _
  simp_rw [he,PiLp.smul_apply,smul_eq_mul]; exact Tendsto.atTop_mul_const hc ht

/-- Transverse translations don't change eventual expectation at large fixed time. -/
lemma rays (H : Fields.Euclidean S) (R : Angular S) (x : Cross a)
    (q : Future F a) : V.flow.U x (V.flow.orth (V.GNS.plant q))=V.flow.orth (V.GNS.plant q) := by
  -- for all p
  have hxq (p : Future F a) : inner ℂ (V.GNS.plant p) (V.flow.U x (V.flow.orth (V.GNS.plant q))) = inner ℂ (V.GNS.plant p) (V.flow.orth (V.GNS.plant q)) := by
    let w := x.val+basis a
    have hw : 0<w a := by simp [w,show x.val a=0 from x.property]
    have h := across_axis V hJ H R w hw (reflect p.val a) q.val (reflects a p.property.1) q.property.1
    let d (i : ℝ≥0) := x.val+(i:ℝ) • basis a
    have hf : Tendsto (fun i : ℝ≥0 => d i a) atTop atTop := by
      simpa [d, show x.val a=0 from x.property] using! (NNReal.tendsto_coe_atTop.mpr (tendsto_id (x := (atTop : Filter ℝ≥0))))
    have ht := overtops V hJ H d hf (reflect p.val a) q.val (reflects a p.property.1) q.property.1 1
    have hy (i : ℝ≥0) : d i+(1:ℝ) • basis a=w+(i:ℝ) • basis a := by simp [d,w]; abel
    simp_rw [hy] at ht
    have he := h.sub ht
    let A i := V.flow.E i (V.GNS.plant q)
    let F := V.GNS.plant p
    have hz : Tendsto (fun i : ℝ≥0 => inner ℂ F (V.flow.U x (A i))-inner ℂ F (A i)) atTop (𝓝 0) := by
      rw [sub_self] at he; refine he.congr' (Eventually.of_forall fun i => ?_)
      have hv : inner ℂ F (V.flow.U x (A i))= _ := going V H p q x i
      have hp := going V H p q (0: Cross a) i
      rw [V.flow.uZero, ContinuousLinearMap.id_apply] at hp
      dsimp only; rw [show inner ℂ F (A i)=_ from hp,hv]; dsimp only [d,ing,Submodule.coe_zero]; rw [zero_add];abel
    apply sub_eq_zero.mp
    have he := V.flow.emerges (V.GNS.plant q)
    exact tendsto_nhds_unique (f := fun i : ℝ≥0 => inner ℂ F (V.flow.U x (A i))-inner ℂ F (A i))
      ((tendsto_const_nhds.inner ((V.flow.U x).continuous.continuousAt.tendsto.comp he)).sub (tendsto_const_nhds.inner he)) hz
  apply V.GNS.whole.eq_of_inner_right ℂ
  intro v; induction v using Finsupp.induction_linear with
  | zero => simp
  | add i j hi hj => simp only [map_add,inner_add_left,hi,hj]
  | single i c => simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left,hxq]

theorem inert (H : Fields.Euclidean S) (R : Angular S) (x : Cross a) (w : V.flow.ground) : V.flow.U x w.val=w.val := by
  have he := V.GNS.by_bud (V := (V.flow.U x).comp V.flow.orth) (fun p => rays V hJ H R x p)
  have hv : V.flow.orth w.val=w.val := V.flow.ground.starProjection_eq_self_iff.mpr w.property
  rw [← show (V.flow.orth w.val)=w.val from hv,← ContinuousLinearMap.comp_apply,he]
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.inert
