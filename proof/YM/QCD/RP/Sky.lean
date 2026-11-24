import YM.Slice.Copies
import YM.QCD.Lattice.Cut
import YM.QCD.Grass.Time

/-!
# A link plane and the anti-linear matter reflection

Use YM.Cells.Cut and YM.Slice layering. Continuous insertions local over strict sites,
compatible with transformations. Seam/sign hypotheses for RP in next modules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lattice Wilson Function Finset Grass Lat
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology
variable {n : Side} {F : ℕ}
variable (R : Cells.Cut n)

def perm : Equiv.Perm (Site n) := Involutive.toPerm R.reflect R.twice
@[simp] lemma permed (x : Site n) : perm R x=R.reflect x := rfl
@[simp] lemma perm_symm : (perm R).symm=perm R := rfl

def lamp (a : Axis) := wave (gamma a)
@[simp] lemma lamp_star (a : Axis) : star (lamp a)=lamp a := by rw [lamp,wave_star,gamma_star]
@[simp] lemma lamp_sq (a : Axis) : lamp a*lamp a=1 := by rw [lamp,wave_mul, gamma_sq,wave_one]

def folds (F : ℕ) := copies F (rides (perm R) fun _ => lamp R.pos)
lemma folds_star (F : ℕ) : star (folds R F)=folds R F := by simp only [folds,← copies_star, ride_ad, lamp_star,perm_symm]
lemma folds_sq (F : ℕ) : folds R F*folds R F=1 := by
  unfold folds
  rw [← copies_mul, ride_mul,show (perm R).trans (perm R)=Equiv.refl _ from
    (Equiv.self_trans_symm _)]
  simp_rw [lamp_sq,ridden,copies_one]

abbrev Wind (F : ℕ) := Fiber × Flavor F
abbrev glow (a : Axis) (F : ℕ) := copies F (lamp a)
@[simp] lemma glow_star (F : ℕ) (a : Axis) : star (glow a F)=glow a F := by rw [glow,← copies_star,lamp_star]
@[simp] lemma glow_sq (F : ℕ) (a : Axis) : glow a F*glow a F=1 := by rw [glow,← copies_mul,lamp_sq,copies_one]

def place {X : Type*} (x : X) (i : Wind F) := ((x,i.1),i.2)

lemma placed {A : Type*} [Fintype A] [DecidableEq A] (e : Equiv.Perm A) (B : A → Bundle)
    (x y : A) (i j : Wind F) : copies F (rides e B) (place x i) (place y j) =
    if e x = y then copies F (B x) i j else 0 := by
  unfold copies; by_cases h : e x=y <;> simp [place,Matrix.blockDiagonal_apply,h,rr]

lemma placed_sum {X M : Type*} [Fintype X] [AddCommMonoid M] (f : ((X × Fiber) × Flavor F) → M) :
    ∑ i,f i=∑ x : X,∑ i : Wind F,f (place x i) := by simp [place, Fintype.sum_prod_type]

lemma tilting_psi {X : Type*} [Fintype X] [DecidableEq X] (e : Equiv.Perm X) (he : e.symm=e)
    (a : Axis) (x : X) (i : Wind F) : tilt (copies F (rides e fun _ => lamp a)) (psi (place x i))=
    ∑ j : Wind F, (-glow a F j i) • bar (place (e x) j) := by
  rw [tilt_psi,placed_sum,sum_eq_single (e x)]
  · have H : e (e x)=x := by nth_rw 1 [← he]; exact e.symm_apply_apply x
    simp [placed,H]
  · intro z _ hz; simp [placed,e.apply_eq_iff_eq_symm_apply,he,hz]
  simp
lemma tilting_bar {X : Type*} [Fintype X] [DecidableEq X] (e : Equiv.Perm X) (a : Axis) (x : X) (i : Wind F) :
    tilt (copies F (rides e fun _ => lamp a)) (bar (place x i))=
    ∑ j : Wind F, (-glow a F i j) • psi (place (e x) j) := by
  rw [tilt_bar,placed_sum,sum_eq_single (e x)]
  · simp [placed]
  · intro z _ hz; simp [placed,hz.symm]
  simp

def theta := tilt (folds R F)
@[simp] lemma theta_psi (x : Site n) (i : Wind F) : theta R (psi (place x i))=
    ∑ j : Wind F, (-glow R.pos F j i) • bar (place (R.reflect x) j) := tilting_psi _ (perm_symm R) ..
@[simp] lemma theta_bar (x : Site n) (i : Wind F) : theta R (bar (place x i))=
    ∑ j : Wind F, (-glow R.pos F i j) • psi (place (R.reflect x) j) := tilting_bar ..
lemma theta_mul (x y : Fields n F) : theta R (x*y)=theta R y*theta R x := tilt_mul ..
lemma theta_turn (x : Fields n F) : theta R (theta R x)=x := untilt _ (folds_star R F) (folds_sq R F) x
lemma theta_grade (x : Fields n F) : grade (theta R x)=theta R (grade x) := tilt_grade ..

/-- Strict (open) sector variables. -/
abbrev Sky := R.sector
instance : Fintype (Sky R) := Fintype.ofFinite _
abbrev Lamp (F : ℕ) := (Sky R × Fiber) × Flavor F

def light (i : Lamp R F) : Modes n F := ((i.1.1.val,i.1.2),i.2)
def dark (i : Lamp R F) : Modes n F := ((R.reflect i.1.1,i.1.2),i.2)

lemma switch (h : R.kind=.link) (x : Site n) : x ∉ R.sector ↔ R.reflect x ∈ R.sector := by
  constructor
  · intro H
    by_contra hs
    apply (Slice.walls_link h).false
    exact ⟨x R.pos,H,by simp_rw [Slice.level,← R.reflect_here]; exact hs⟩
  intro H hx; exact R.link_switch h hx H

lemma enroll (h : R.kind=.link) : Bijective (Sum.elim (dark R (F:=F)) (light R (F:=F))) := by
  have he (i j : Lamp R F) : dark R i ≠ light R j := fun H => R.link_switch h i.1.1.property (by
    have hq : R.reflect i.1.1 = j.1.1 := congrArg (fun k => k.1.1) H; rw [hq]; exact j.1.1.property)
  constructor
  · rintro (i|i) (j|j) H
    · rw [show i=j from Prod.ext (Prod.ext (Subtype.ext ((perm R).injective
        (show R.reflect i.1.1=R.reflect j.1.1 from congrArg (fun k => k.1.1) H))) (congrArg (fun k => k.1.2) H)) (congrArg (fun k => k.2) H)]
    · exact (he _ _ H).elim
    · exact (he _ _ H.symm).elim
    rw [show i=j from Prod.ext (Prod.ext (Subtype.ext (congrArg (fun k => k.1.1) H)) (congrArg (fun k => k.1.2) H)) (congrArg (fun k => k.2) H)]
  rintro ⟨⟨x,i⟩,f⟩
  classical
  by_cases hx : x ∈ R.sector
  · exact ⟨Sum.inr ((⟨x,hx⟩,i),f),rfl⟩
  exact ⟨Sum.inl ((⟨R.reflect x,(switch R h x).mp hx⟩,i),f),by simp [dark]⟩

def innerFold (F : ℕ) := copies F (rides (Equiv.refl (Sky R)) (fun _ => lamp R.pos))
lemma inner_turn (F : ℕ) : innerFold R F*innerFold R F=1 := by
  unfold innerFold; rw [← copies_mul,ride_mul]; simp_rw [Equiv.refl_trans,lamp_sq,ridden,copies_one]

lemma shaded (z : Dirac (Lamp R F)) : theta R (pass (light R) z) = pass (dark R) (tilt (innerFold R F) z) := by
  let T := (theta R).comp (pass (light R (F:=F))).toLinearMap
  let H := (pass (dark R)).toLinearMap.comp (tilt (innerFold R F))
  suffices T=H by change T z = H z; rw [this]
  apply ext_reversing (by intro x y; simp only [T,map_mul,theta_mul,LinearMap.comp_apply,AlgHom.toLinearMap_apply])
    (by intro x y; simp only [H,map_mul,tilt_mul,LinearMap.comp_apply,AlgHom.toLinearMap_apply]) (by simp [T,H,theta])
  rintro (⟨⟨x,i⟩,f⟩|⟨⟨x,i⟩,f⟩)
  · change theta R (pass _ (psi (place x (i,f))))=pass (dark R) (tilt (copies _ _) (psi (place x (i,f))))
    rw [pass_psi, show light R (place x (i,f)) = place x.val (i,f) from rfl,theta_psi,
      tilting_psi (Equiv.refl _) rfl,map_sum]; simp only [map_smul,pass_bar]; rfl
  change theta R (pass _ (bar (place x (i,f))))=pass (dark R) (tilt (copies _ _) (bar (place x (i,f))))
  rw [pass_bar,show light R (place x (i,f)) = place x.val (i,f) from rfl,theta_bar,tilting_bar,map_sum]
  simp only [map_smul,pass_psi]; rfl

lemma overlap (h : R.kind=.link) (w z : Dirac (Lamp R F)) :
    ber (Modes n F) (theta R (pass (light R) w)*pass (light R) z) = star (ber _ w)*ber _ z := by
  rw [shaded, complementary _ _ (dark R) (light R) (enroll R h), tilt_amp (innerFold R F) (inner_turn ..)]

/-- Formulate strict support by fields in the positive algebra and no gauge links beyond its
endpoints. Does not require positivity or invariance yet. -/
def Sided (x : Insertion n F) : Prop :=
  ∃ f : Grid n → Dirac (Lamp R F), Continuous f ∧ LocalOn R.sector f ∧ ∀ U, x U=pass (light R) (f U)

def reflect (x : Insertion n F) : Insertion n F :=
  ⟨fun U => theta R (x (R.pullC su U)), (tilt_cont _).comp (x.continuous.comp (Wilson.continuous_pull _ _))⟩
@[simp] lemma reflects (x : Insertion n F) (U) : reflect R x U = theta R (x (R.pullC su U)) := rfl
lemma reflects_inv (x : Insertion n F) : reflect R (reflect R x)=x := by ext1 i; simp [theta_turn]
lemma reflects_mul (x y : Insertion n F) : reflect R (x*y)=reflect R y * reflect R x := by ext1 U; exact theta_mul ..

lemma face_rot (s : Signed) (t : Site n) (k : Frame n) (U : Grid n) :
    pull s t (gauge k U)=gauge (k ∘ affine s t) (pull s t U) := by
  funext e; unfold Lattice.gauge pull
  simp only [comp_apply]; rw [show affine s t (e.1+step e.2) = affine s t e.1 + ((posDir e.2).rotate s).vec by rw [Step.vec_rotate]; simp [affine]; abel]; exact Step.gauge_read ..
lemma arms (F : ℕ) (k : Frame n) : folds R F*rotates F k=rotates F (k ∘ R.reflect)*folds R F := by
  unfold folds rotates; rw [← copies_mul,← copies_mul]; unfold siteRot
  rw [ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 2; funext x; exact (interlace ..).symm
lemma respects (k : Frame n) (x : Insertion n F) :
    transform k (reflect R x) = reflect R (transform (k ∘ R.reflect) x) := by
  ext1 U
  change slots F k (theta R (x (pull _ _ (gauge k U)))) = theta R (slots _ _ (x (gauge _ _)))
  rw [face_rot]; exact (tilt_through _ _ _ _ (folds_star ..) (folds_star ..) (arms R F k) _).symm
lemma reflect_invariant (x : Insertion n F) (H : Invariant x) : Invariant (reflect R x) := fun k => by rw [respects,H]
end YM.QCD.RP
