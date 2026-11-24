import YM.MassiveBridge.Flow
import YM.OS.Core

/-!
# Bounded insertion between strictly positive time gaps

As in `YM.OS.Slabs`, preserve the exact order of factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter Analysis
open Fields (distinct prepend pointMoment)
open OS (Cross)
open scoped Topology NNReal BigOperators ContDiff InnerProductSpace ComplexOrder
variable {F : Fields} {S : F.Kernel}
variable (a : Axis)

def Slab (d : ℝ≥0) (w : Cluster F) := 0<d ∧ Positive w a ∧ ∀ p ∈ w, p.1 a < (d:ℝ)

def buffer (r : ℝ) (d : ℝ≥0) (w : Cluster F) := spaced r (positions w) ∧
  ∀ p ∈ w, r ≤ p.1 a ∧ p.1 a ≤ (d:ℝ)-r

def raised (d : ℝ≥0) (v : Cluster F) := carry v ((d:ℝ) • basis a)

def linked (d : ℝ≥0) (v w : Cluster F) : Cluster F := v ++ raised a d w

def opposite (d : ℝ≥0) (v : Cluster F) := raised a d (reflect v a)

variable {a}

lemma appendsFuture {v w : Cluster F} {d} (h : Slab a d v) (hp : Positive w a) : Positive (linked a d v w) a := by
  have he := (travel (⟨w,hp⟩ : Future F a) d).property
  let F := raised a d w
  have ht : Positive F a := he
  refine ⟨?_, ?_⟩
  · unfold linked
    rw [locations,List.map_append,List.nodup_append]
    refine ⟨locations.mp h.2.1.1,locations.mp ht.1,?_⟩
    intro _ hx y hy; obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    intro he; change p.1=s.1+_ at he
    have hv := h.2.2 p hp'
    rw [he] at hv; simp at hv
    exact hv.not_ge (hp.2 s hs).le
  intro p hu; exact (List.mem_append.mp hu).elim (fun hp => h.2.1.2 p hp) (fun hp => ht.2 p hp)

lemma mirrorsSlab {v : Cluster F} {d} (hx : Slab a d v) : Slab a d (opposite a d v) := by
  have he p (hp : p∈opposite a d v) : 0<p.1 a ∧ p.1 a < (d:ℝ) := by
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hp
    rw [reflectedPoint,List.mem_map] at hu
    obtain ⟨w,hw,rfl⟩ := hu
    have hv := List.mem_reverse.mp hw
    have ht := hx.2.1.2 w hv
    have hh := hx.2.2 w hv
    simp [Signed.mirrored]; constructor <;> linarith
  exact ⟨hx.1,⟨still (reflects a hx.2.1.1) _, fun p hp => (he p hp).1⟩, fun p hp => (he p hp).2⟩

lemma connects {v w : Cluster F} {d e} (h : Slab a d v) (hh : Slab a e w) : Slab a (d+e) (linked a d v w) := by
  refine ⟨add_pos h.1 hh.1,appendsFuture h hh.2.1,?_⟩
  intro i hI; cases List.mem_append.mp hI with
  | inl hv => exact (h.2.2 i hv).trans_le (by simp)
  | inr hw =>
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
    have hp := hh.2.2 x hx; simp; linarith

lemma vacuum_width {d : ℝ≥0} (h : 0<d) : Slab (F := F) a d [] := ⟨h,(air (F := F) a).property,by simp⟩

lemma invol (a : Axis) (h : Function.Involutive (F.adj a)) (u) (v : Cluster F) : opposite a u (opposite a u v) = v := by
  unfold opposite raised
  rw [refl_over, reflect_twice a h, paths]
  rw [show Ortho.move (Signed.reflect a) ((u:ℝ) • basis a) = - ((u:ℝ) • basis a) by
    ext i; by_cases h : i=a <;> simp [Signed.mirrored,h], neg_add_cancel, rest]

def entering {d} {u : Cluster F} (hx : Slab a d u) (v : Future F a) : Future F a :=
  ⟨linked a d u v.val, appendsFuture hx v.property⟩

@[simp] lemma when_empty {d} (h : Slab (F := F) a d []) (v : Future F a) : entering h v = travel v d := rfl

lemma connected {d e} {u v : Cluster F} (hp : Slab a d u) (he : Slab a e v) (z : Future F a) :
    entering (connects hp he) z=entering hp (entering he z) := by
  apply Subtype.ext; simp [entering,linked,raised, add_smul,add_comm]

lemma realignment {u : Cluster F} {d} (w : Slab a d u) (h : Fields.Euclidean S) (x y : Future F a) :
    kernel S a (entering w x).val y.val = kernel S a x.val (entering (mirrorsSlab w) y).val := by
  let t : E4 := (d:ℝ) • basis a
  unfold kernel
  rw [← invariance h (twoSides (entering w x).property y.property) t]
  congr 1
  have he (u v : Cluster F) : reflect (u++v) a = reflect v a ++ reflect u a := by simp [reflectedPoint]
  change carry (reflect (u ++ carry x.val t) a ++ y.val) t = _
  rw [he,distribute,distribute,refl_over, paths, show Ortho.move (Signed.reflect a) t = -t by
    ext i; by_cases h : i=a <;> simp [Signed.mirrored,t,h], neg_add_cancel, rest,listEq]
  rfl
where listEq (u v z : Cluster F) : (u++v)++z = u++(v++z) := List.append_assoc ..

structure Spread (V : Chamber S a) where
  place (d : ℝ≥0) (w : Cluster F) : V.GNS.H.Op
  reads {d : ℝ≥0} {w : Cluster F} (h : Slab a d w) (p : Future F a) :
    place d w (V.GNS.plant p) = V.GNS.plant (entering h p)

namespace Spread
variable {V : Chamber S a} (P : Spread V)

lemma blank {d} (h : 0 < d) : P.place d []=V.flow.E d :=
  V.GNS.by_bud fun i => (P.reads (vacuum_width h) _).trans (V.atBirth d i)

lemma concatenate {d e} {u v : Cluster F} (h : Slab a d u) (he : Slab a e v) :
    P.place (d+e) (linked a d u v) = (P.place d u).comp (P.place e v) := by
  apply V.GNS.by_bud; intro i
  rw [ContinuousLinearMap.comp_apply,P.reads he,P.reads h, P.reads (connects h he),connected h he]

lemma adjoints {d} {u : Cluster F} (h : Slab a d u) (hv : Fields.Euclidean S) (hh : Function.Involutive (F.adj a)) :
    (P.place d u).adjoint = P.place d (opposite a d u) := by
  apply V.GNS.by_bud; intro x
  refine V.GNS.whole.eq_of_inner_left ℂ fun f => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add i j hi hj => simp only [map_add,inner_add_right,hi,hj]
  | single i c =>
    simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul,
      inner_smul_right,P.reads h _,P.reads (mirrorsSlab h) _,V.GNS.measure]
    congr 1
    -- lhs input intermediate earlier than counterpart; use reflect twice
    rw [realignment (mirrorsSlab h) hv]; exact congr_arg (kernel S a _) (show _ from by simp [entering,linked, invol a hh])

lemma over_word (s : Cross a) {d} {u : Cluster F} (h : Slab a d u) :
    Slab a d (carry u s.val) := by
  refine ⟨h.1,(over (⟨u,h.2.1⟩ : Future F a) s).property,?_⟩
  intro i hi; obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
  simpa [show s.val a=0 from s.property] using h.2.2 _ hw

lemma perpendicular {d} {u : Cluster F} (h : Slab a d u) (s : Cross a) :
    (V.flow.U s).comp (P.place d u) = (P.place d (carry u s.val)).comp (V.flow.U s) := by
  apply V.GNS.by_bud; intro v
  simp only [ContinuousLinearMap.comp_apply,P.reads h _,← V.across s _, P.reads (over_word s h) _]
  apply congr_arg; apply Subtype.ext
  simp [over,entering,linked,raised, add_comm]

variable {d e : ℝ≥0} {w : Cluster F}
lemma swelling (h : Slab a d w) (u : ℝ≥0) : Slab a (d+u) w :=
  ⟨add_pos_of_pos_of_nonneg h.1 (show _ from bot_le),h.2.1,fun i hi => lt_of_lt_of_le (h.2.2 _ hi) (by simp)⟩
lemma stretches (h : Slab a d w) (u : ℝ≥0) : P.place (d+u) w=(P.place d w).comp (V.flow.E u) := by
  apply V.GNS.by_bud; intro i
  rw [ContinuousLinearMap.comp_apply,P.reads (swelling h u) i, ← V.atBirth, P.reads h]; congr 1
  apply Subtype.ext
  simp [entering,linked,raised,travel,add_comm, add_smul]
lemma fills (h : Slab a d w) (u : ℝ≥0) : Slab a (u+d) (raised a u w) := by
  rcases eq_or_ne u 0 with h'|h'
  · subst u; simpa [raised] using h
  exact connects (vacuum_width (pos_iff_ne_zero.mpr h')) h
lemma crossing (h : Slab a d w) (u : ℝ≥0) : P.place (u+d) (raised a u w)=(V.flow.E u).comp (P.place d w) := by
  rcases eq_or_ne u 0 with h'|h'
  · subst u; simp [raised,V.flow.eZero]
  rw [← P.blank (pos_iff_ne_zero.mpr h'), ← P.concatenate (vacuum_width (pos_iff_ne_zero.mpr h')) h]; rfl

end Spread
namespace Chamber
variable (C : Chamber S a)
abbrev H : Hilbert := C.GNS.H
abbrev D : Submodule ℂ C.H := C.flow.ground
def omega : C.H := C.GNS.plant (air a)
def omega0 : C.D := ⟨C.omega, (C.flow.fixed _).2 fun t => (C.atBirth t _).symm.trans
  (congr_arg C.GNS.plant (inAir t))⟩
def UniqueHeat : Prop := ∀ v : C.D, ∃ z : ℂ, v = z • C.omega0
end Chamber
end YM.Massive.Bridge
