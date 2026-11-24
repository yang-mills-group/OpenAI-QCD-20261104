import YM.QCD.RP.Cross
import YM.QCD.RP.Door

/-!
# Split coupled stencil on one plane with compatible seam

Positive-side summand, reflected copy, and explicitly exhibited
kinetic cross form independent of internal fields after gauge choice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lattice Wilson Grass Lat NormedSpace Function Slice Slice.Link
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology

variable {n : Side} {R : Cells.Cut n} {F : ℕ}
local notation "v" => R.pos
local notation "b" => Link.bottom R
local notation "c" => Link.top R
local notation "φ" => plane v
local notation "o" => Open R su
local notation "V" => Slice.Row v n

/-- Antiperiodic seam sits opposite the start of the positive half. For
other cuts introduce later equivalence moving the seam. -/
def Matches (C : Lat.Cut n F) (R : Cells.Cut n) := C.t R.pos=Link.top R+1
lemma exit_plus (h : R.kind=.link) (x : V) : φ c x∈R.sector := by change Slice.Plus R _; rw [plane_pos]; exact (leaving_top h).1
lemma entry_plus (h : R.kind=.link) (x : V) : φ (b+1) x∈R.sector := by change Slice.Plus R _; rw [plane_pos]; exact (below_base h).2

def joint (R : Cells.Cut n) (F : ℕ) : Fields n F :=
  (∑ x : Slice.Row R.pos n, spans F R.pos 1 (plane R.pos (bottom R) x) (plane R.pos (bottom R+1) x))+
  (∑ x : Slice.Row R.pos n, spans F R.pos (-1) (plane R.pos (Link.top R) x) (plane R.pos (Link.top R+1) x))

lemma joint_even (F : ℕ) (h : R.kind=.link) : Grass.Plus (joint R F) ∧ Matinee R (exp (joint R F)) := by
  refine twain (panels _ _ ?_) (panels _ _ ?_)
  · intro i _
    have H := leading (F:=F) (⟨φ (b+1) i,entry_plus h i⟩ : Sky R)
    simpa only [image_plane,chord_end,br h] using H
  intro i _
  have H := trailing (F:=F) (⟨φ c i,exit_plus h i⟩ : Sky R)
  have he : level R c = c+1 := by simpa only [imageChord,sub_eq_iff_eq_add] using tr h
  simpa only [image_plane,he] using H

-- Sector geometry wraps

def daylight (i : Inner R) (x : V) : Sky R := ⟨φ i x, by change Slice.Plus R _; rw [plane_pos]; exact i.property⟩
lemma either_plus (h : R.kind=.link) {z : Per n} (hx : ¬ Slice.Plus R (level R z)) : Slice.Plus R z := by
  by_contra hz; exact (walls_link h).false ⟨z,hz,hx⟩

def into (h : R.kind=.link) (i : Steps R) : Inner R := ⟨i,either_plus h (thread_ends i.property).1⟩
def toward (h : R.kind=.link) (i : Steps R) : Inner R := ⟨i.val+1,either_plus h (thread_ends i.property).2⟩

variable (C : Lat.Cut n F)

def deck (X : o) (i : Inner R) : Dirac (Lamp R F) := ∑ x : V,
  (bank (C.m+4) F (daylight i x) + ∑ a : Flat v, spans F a.val
    (Lat.seam C.t (φ i x) a.val • colour (X.1 i (x,a))) (daylight i x) (daylight i (Slice.forward v x a)))

def fast (h : R.kind=.link) (X : o) (i : Steps R) : Dirac (Lamp R F) :=
  ∑ x : V, spans F v (colour (X.2 i x)) (daylight (into h i) x) (daylight (toward h i) x)
-- C unused?

def fence (h : R.kind=.link) (X : o) := (∑ i, deck C X i) + ∑ i, fast (F:=F) h X i
@[fun_prop] lemma fence_c (h : R.kind=.link) : Continuous (fence C h) := by unfold fence deck fast; fun_prop

lemma deck_even (X : o) (i : Inner R) : Grass.Plus (deck C X i) := Hom.sum (p:=false) fun x _ =>
  Hom.add (p:=false) (linkB_even ..) (Hom.sum (p:=false) (fun y _ => spans_even ..))
lemma fence_even (h : R.kind=.link) (X : o) : Grass.Plus (fence C h X) := Hom.add (p:=false)
  (Hom.sum (p:=false) fun _ _ => deck_even ..) (Hom.sum (p:=false) fun _ _ => Hom.sum (p:=false) fun _ _ => spans_even ..)

-- Verify by comparing all site sums.
def levelTerm (U : Grid n) (R : Cells.Cut n) (t : Per n) := ∑ x : Slice.Row R.pos n,
    (bank (C.m+4) F (plane R.pos t x)+∑ a : Flat R.pos, hopTerm C U (plane R.pos t x) a)
def slope (U : Grid n) (R : Cells.Cut n) (t : Per n) := ∑ x : Slice.Row R.pos n, hopTerm C U (plane R.pos t x) R.pos

lemma main_calendar (U : Grid n) : form (C.ferm U) = (∑ i,levelTerm C U R i) + ∑ i,slope C U R i := by
  let e : (Per n × V) ≃ Site n :=
    { toFun := fun x => φ x.1 x.2, invFun := fun x => (x v,drop v x), left_inv := fun x => by simp
      right_inv := fun x => by simp }
  have he (f : Site n→Fields n F) : (∑ x,f x)=∑ i,∑ x : V,f (φ i x) := by
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]; rfl
  have hb (f : Axis → Fields n F) : ∑ a, f a=(∑ a : Flat v,f a)+f v := by
    let g : Flat v ⊕ Unit ≃ Axis :=
      { toFun := Sum.elim Subtype.val fun _ => v, invFun := fun a => if h : a=v then Sum.inr () else Sum.inl ⟨a,h⟩
        left_inv := fun x => by cases x with
                               | inl i => simp [i.property]
                               | inr i => simp
        right_inv := fun x => by by_cases h : x=v <;> simp [h] }
    rw [← Equiv.sum_comp g, Fintype.sum_sum_type]; simp [g]
  rw [bare_basis,he, he (fun x => ∑ a : Axis, hopTerm C U x a)]; unfold levelTerm slope
  simp_rw [hb,Finset.sum_add_distrib]; abel

variable {C}
lemma aligned (h : Matches C R) (t : Per n) (ht : t ≠ c) (x : V) : Lat.seam C.t (φ t x) v=1 := by
  simp [Lat.seam,(show C.t v = _ from h),ht]

lemma colour1 : colour (1:su.El)=1 := su.mat_one

lemma cleared_terms (h : R.kind=.link) (T : Matches C R) (X Y : o) :
    slope C (RP.clear R X Y) R b+slope C (RP.clear R X Y) R c=joint R F := by
  have ha (i : ↥(gate R)) (x : V) : RP.clear R X Y (φ i x,v)=1 := by rw [RP.clear, chain_time, follow, checkpoint]; rfl
  have hb (x) : thread C.t (RP.clear R X Y) v (φ b x)=1 := by rw [thread,show RP.clear R X Y (φ b x,v)=1 from ha (ebb h) x,aligned T _ piers_split,one_smul,colour1]
  have hc (x) : thread C.t (RP.clear R X Y) v (φ c x) = -1 := by rw [thread,show RP.clear R X Y (φ c x,v)=1 from ha (high h) x, show Lat.seam C.t (φ c x) v = -1 by simp [Lat.seam,(show C.t v=_ from T)], colour1, neg_smul,one_smul]
  unfold slope hopTerm joint; simp_rw [hb,hc,lift_time]

variable (C)
private lemma sunny (X Y : o) (i : Inner R) : levelTerm C (RP.clear R X Y) R i = pass (light R) (deck C X i) := by
  unfold levelTerm deck hopTerm
  simp_rw [map_sum,map_add,map_sum,surface,bank,passB,daylight,RP.clear,thread,Slice.shift,chain_space,follow,Slice.hit]
private lemma moon (X Y : o) (i : Inner R) : levelTerm C (RP.clear R X Y) R (level R i) = theta R (pass (light R) (deck C Y i)) := by
  have H (m) (x : Sky R) : pass (light R) (bank m F x)=bank m F x.val := passB ..
  have hx (a : Flat v) (t : Per n) (x : V) : Lat.seam C.t (φ (level R t) x) a = Lat.seam C.t (φ t x) a := by simp [Lat.seam]
  unfold levelTerm deck hopTerm
  simp_rw [map_sum,map_add,map_sum,H,surface,theta_bank, fun a : Flat v => tang_span (F:=F) (n:=n) R a.property,
    daylight,image_plane,RP.clear,thread,hx,Slice.shift,chain_space,follow,hitOpp]; rfl

variable {C}
lemma wire_up (h : R.kind=.link) (T : Matches C R) (X Y : o) (i : Steps R) :
    slope C (RP.clear R X Y) R i= pass (light R) (fast h X i) := by
  have hi : i.val ≠ c := by intro he; exact (high h).property.1 (show bridge R c from he ▸ i.property)
  unfold slope fast hopTerm; simp_rw [map_sum,surface,thread,aligned T i hi, one_smul,lift_time,
    RP.clear,chain_time,follow,pointed]; rfl
lemma wire_down (h : R.kind=.link) (T : Matches C R) (X Y : o) (i : Steps R) :
    slope C (RP.clear R X Y) R (imageChord R i)= theta R (pass (light R) (fast h Y i)) := by
  have hi : imageChord R i.val ≠ c := by
    intro he
    have hz := congrArg (imageChord R) he
    rw [chord_turn,tr h] at hz
    exact (high h).property.1 (show bridge R c from hz ▸ i.property)
  unfold slope fast hopTerm; simp_rw [map_sum,surface,chord_span,thread,aligned T _ hi, one_smul,lift_time,
    RP.clear,chain_time,follow,pointed_back]
  unfold daylight into toward; simp only [image_plane,chord_end]
  have he (y) : imageChord R y+1=level R y := by unfold imageChord; abel
  simp [he, replace]

lemma gangs (h : R.kind=.link) : Bijective (Sum.elim (fun i : Inner R => i.val) (fun i : Inner R => level R i.val)) := by
  constructor
  · rintro (i|i) (j|j) H
    · rw [show i=j from Subtype.ext H]
    · exact (opposite_leaf j.property ((show i.val=level R j from H) ▸ i.property)).elim
    · exact (opposite_leaf i.property ((show j.val=level R i from H.symm) ▸ j.property)).elim
    have hw : Involutive (level R) := level_twice R
    rw [show i=j from Subtype.ext (hw.injective H)]
  intro x
  classical
  by_cases hx : Slice.Plus R (level R x)
  · exact ⟨Sum.inr ⟨_,hx⟩,level_twice R x⟩
  exact ⟨Sum.inl ⟨_,either_plus h hx⟩,rfl⟩

theorem gathering (h : R.kind=.link) (T : Matches C R) (X Y : o) :
    form (C.ferm (RP.clear R X Y)) = joint R F + (theta R (pass (light R) (fence C h Y))+pass (light R) (fence C h X)) := by
  classical
  rw [main_calendar (R:=R),← Equiv.sum_comp (Equiv.ofBijective _ (gangs h))]
  let U := RP.clear R X Y
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (class_bijection R)) (slope C U R)]
  simp only [Fintype.sum_sum_type,Equiv.ofBijective_apply,Sum.elim_inl,Sum.elim_inr]
  have hs : ∑ i : ↥(gate R), slope C U R i.val=joint R F := by
    rw [show (Finset.univ : Finset ↥(gate R)) = {ebb h,high h} from
      Finset.ext fun i => by simp [points_into h i], Finset.sum_pair (Link.clear h)]; exact cleared_terms h T X Y
  simp only [U] at hs ⊢
  rw [hs]; simp_rw [sunny, moon,wire_up h T,wire_down h T,fence,map_add,map_sum]; abel

lemma dress (h : R.kind=.link) (T : Matches C R) (X Y : o) :
    C.insertD (RP.clear R X Y) = exp (joint R F) * RP.hit R (exp (fence C h Y)) (exp (fence C h X)) := by
  have ha (x : o) : Grass.Plus (pass (light R) (fence C h x)) := by unfold Grass.Plus; rw [pass_grade,show grade (fence C h x)=_ from fence_even ..]
  rw [Lat.Cut.insertD_apply,gauss,gathering h T,algebra_exp_add ((joint_even F h).1.central _).symm,algebra_exp_add ((ha _).central _), theta,← tilt_exp,← map_weight, ← map_weight]; rfl
end YM.QCD.RP
