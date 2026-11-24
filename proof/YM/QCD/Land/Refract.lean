import YM.QCD.Land.Remote
import YM.QCD.RP.Reflector

/-!
# Reflection of local tests and thermodynamic compatibility
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Land
open Lat Lattice Wilson Grass RP Function Finset Extraction Filter Topology
open scoped BigOperators Matrix.Norms.Frobenius Matrix ComplexOrder

variable {F : ℕ} {n : Side} {D S K : Lot}

-- transport links. Works for any containing lot. use for translations as well
section Pull
variable (s : Signed) (t : Cover) (h : Set.MapsTo (affine s t) ↑D ↑S)

def pushes (x : Court D) : Court S := ⟨affine s t x.val,h x.property⟩
def pushp (i : Pad D F) : Pad S F := ((pushes s t h i.1.1,i.1.2),i.2)

def repute (V : Trace S) : CoverConfig su := Function.extend (coveredge (D:=S)) V 1
lemma reputed (V : Trace S) : inspects (repute V)=V := funext fun _ => coveredge_inj.extend_apply ..

@[fun_prop] lemma reputed_cont : Continuous (repute (S:=S)) := by
  apply continuous_pi; intro i
  by_cases hi : ∃ j : Pipe S,coveredge j=i
  · obtain ⟨j,rfl⟩ := hi; simp_rw [show ∀ x : Trace S,repute x (coveredge j)=_ from fun x => congr_fun (reputed x) j]; exact continuous_apply _
  have hv (x : Trace S) : repute x i=1 := Function.extend_apply' x _ _ hi
  simp_rw [hv]; exact continuous_const

def lenses (_h : Set.MapsTo (affine s t) ↑D ↑S) (V : Trace S) : Trace D := inspects (pull s t (repute V))
@[fun_prop] lemma lenses_cont : Continuous (lenses s t h) := by
  apply continuous_pi; intro i
  unfold lenses inspects pull Step.read; split <;> fun_prop

lemma pipe_view (U V : CoverConfig su) : inspects (D:=D) U=inspects V ↔ Agrees (R:=ℤ) ↑D U V := by
  constructor
  · intro H e hi hj; rcases e with ⟨x,j⟩
    have he : (⟨x,hi⟩ : Court D).val+step j ∈ D := hj
    exact congr_fun H (⟨((⟨x,hi⟩ : Court D),j),he⟩ : Pipe D)
  intro H; exact funext fun i => H (coveredge i) (inlet i).property i.property
lemma leg (x : Cover) (a : Axis) : affine s t (x+step a)=affine s t x+((posDir a).rotate s).vec := by rw [Step.vec_rotate]; simp [affine]; abel
include h
lemma sees_c (U V : CoverConfig su) (e : Agrees ↑S U V) : Agrees (R:=ℤ) (K:=su.El) ↑D (pull s t U) (pull s t V) := by
  -- `include h`
  intro d H K
  have h₁ := h H; have h₂ := h K
  rw [leg] at h₂
  let i := (posDir d.2).rotate s
  change i.read U _ = i.read V _
  change affine s t d.1 + i.vec ∈ _ at h₂
  have hh : U (i.used (affine s t d.1))=V (i.used (affine s t d.1)) := by
    unfold Step.used; split
    next ht => exact e _ (by simpa [sub_eq_add_neg,Step.vec,ht] using h₂) (by simpa using h₁)
    next ht => exact e _ h₁ (by simpa [Step.vec,ht] using h₂)
  unfold Step.read; rw [hh]
lemma lenses_at (U : CoverConfig su) : lenses s t h (inspects U)=inspects (pull s t U) := by
  unfold lenses; apply (pipe_view ..).mpr
  exact sees_c s t h _ _ ((pipe_view _ _).mp (reputed _))

omit h in
lemma open_pull (U : Grid n) : expandAt (0 : Site n) (pull s (wrap n t) U)=pull s t (expandAt 0 U) := by
  rw [expandAt_pull]; simp only [affine,Signed.act_zero,zero_add]
  funext i
  unfold pull Step.read Step.used affine expandAt
  split <;> (first | split | skip) <;> simp [map_sub,wrap_step,add_sub_right_comm]
lemma lenses_wrap (U : Grid n) : lenses s t h (wraps n U)=wraps n (pull s (wrap n t) U) := by
  simp_rw [inspects_wrap]; rw [lenses_at,open_pull]
end Pull

structure Wall where
  axis : Axis
  post : ℤ
namespace Wall
variable (W : Wall)

abbrev mirror := Signed.mirror W.axis
def save : Cover := (2*W.post-1) • step W.axis
def wall (t : ℕ) : Cells.Cut (spanT t) := ⟨half t, twice t, .link, W.axis,W.post⟩
def walks (x : Cover) := affine W.mirror W.save x
def Within (D S : Lot) := Set.MapsTo W.walks ↑D ↑S
def stands (D : Lot) := ∀ x : Court D,W.post ≤ x.val W.axis
def guide : Cover := W.post • step W.axis

@[simp] lemma walking (x) : W.walks (W.walks x) = x := by
  unfold walks affine; ext1 i
  by_cases h : i=W.axis; · simp [save,h,Signed.mirror,Signed.act]; abel
  simp [save,h,Signed.mirror,Signed.act,h,Ne.symm h]
lemma slides (t : ℕ) : (W.wall t).slide=wrap (spanT t) W.save := by
  simp only [Cells.Cut.slide,wall,save,map_zsmul,wrap_step]
  ext1 i; by_cases h : i=W.axis <;> simp [h,Pi.smul_apply,Cells.Kind.shift] <;> ring
lemma wrap_walk (x : Cover) (t) : (W.wall t).reflect (wrap (spanT t) x)=wrap (spanT t) (W.walks x) := by
  rw [Cells.Cut.reflect,walks]; unfold affine; rw [map_add, wrap_signed, W.slides]; rfl
lemma seals (F β m t) : Matches (relay F β m W.guide t) (W.wall t) := by
  unfold Matches relay wall Slice.Link.top seamPoint; simp [guide,add_comm]

-- Dirac variables at the wall
def flips (h : W.Within D S) := (pass (pushp (F:=F) W.mirror W.save h)).toLinearMap.comp
  (tilt (copies F (rides (Equiv.refl (Court D)) fun _ => lamp W.axis)))

lemma shines (h : W.Within D S) (t) (x : Poly D F) : pass (allot (spanT t)) (W.flips h x)=theta (W.wall t) (pass (allot _) x) := by
  let U := (pass (allot (D:=S) (F:=F) (spanT t))).toLinearMap.comp (W.flips h)
  let V := (theta (W.wall t)).comp (pass (allot (D:=D) (F:=F) (spanT t))).toLinearMap
  apply LinearMap.congr_fun (f := U) (g := V)
  apply ext_reversing (by intro x y; simp only [U,flips,LinearMap.comp_apply,tilt_mul,AlgHom.toLinearMap_apply,map_mul])
    (by intro x y; simp only [V,LinearMap.comp_apply, AlgHom.toLinearMap_apply,map_mul,theta_mul]) (by simp [U,V,flips,theta])
  rintro (⟨⟨u,j⟩,k⟩|⟨⟨u,j⟩,k⟩)
  · change pass _ (pass _ (tilt (copies _ _) (psi (place u (j,k)))))=theta (W.wall t) (pass _ (psi (place u (j,k))))
    rw [tilting_psi (Equiv.refl (Court D)) rfl,pass_psi (allot _) (place u (j,k)),show allot (spanT t) (place u (j,k))=place (wrap (spanT t) u.val) (j,k) from rfl,theta_psi]
    simp only [map_sum,map_smul,pass_bar,wrap_walk]; rfl
  change pass _ (pass _ (tilt (copies _ _) (bar (place u (j,k)))))=theta (W.wall t) (pass _ (bar (place u (j,k))))
  rw [tilting_bar (Equiv.refl (Court D)),pass_bar (allot _) (place u (j,k)), show allot (spanT t) (place u (j,k))=place (wrap (spanT t) u.val) (j,k) from rfl, theta_bar]
  simp only [map_sum,map_smul,pass_psi,wrap_walk]; rfl

def wake (h : W.Within D S) (x : Cyl D F) : Cyl S F :=
  ⟨fun V => W.flips h (x (lenses W.mirror W.save h V)),by
    let f := tilt (copies F (rides (Equiv.refl (Court D)) fun _ => lamp W.axis))
    have hf : Continuous f := tilt_cont _
    let g := (pass (pushp (F:=F) W.mirror W.save h)).toLinearMap
    have hg : Continuous g := g.continuous_of_finiteDimensional
    exact (hg.comp hf).comp (x.continuous.comp (lenses_cont ..))⟩
lemma wakes (h : W.Within D S) (x : Cyl D F) (t) : issue (spanT t) (W.wake h x)=RP.reflect (W.wall t) (issue _ x) := by
  ext1 i; rw [issued]; change pass _ (W.flips h (x (lenses _ _ h _)))=_
  rw [lenses_wrap,shines,RP.reflects,issued,Cells.Cut.pullC, W.slides]; rfl

lemma tactical (D : Lot) (h : W.stands D) : ∀ᶠ t : ℕ in atTop, Set.MapsTo (wrap (spanT t)) ↑D (W.wall t).sector := by
  have he (u : Court D) : ∀ᶠ t : ℕ in atTop, wrap (spanT t) u.val∈(W.wall t).sector := by
    let x := u.val W.axis-W.post
    have hp := h u
    have hv : 0 ≤ x := by unfold x; omega
    filter_upwards [half_trend.eventually (eventually_gt_atTop x.toNat)] with t ht
    change (Int.cast (R:=Per (spanT t)) (u.val W.axis) - W.post).val < (half t).val
    rw [← Int.cast_sub]
    change (x:Per (spanT t)).val < _
    rw [← Int.toNat_of_nonneg hv,Int.cast_natCast,ZMod.val_natCast_of_lt]; exact ht
    rw [twice]; omega
  filter_upwards [eventually_all.mpr he] with t ht
  intro x hx; exact ht ⟨x,hx⟩

variable {β m : ℝ} {k : Extraction.Sequence} {f : LocalState F} (h : Exhausts β m k f)
include h
lemma relation (hp : W.Within D S) (x : Cyl D F) : f.amp S (W.wake hp x)=star (f.amp D x) := by
  apply tendsto_nhds_unique (world (W.wake hp x) h W.guide)
    (((world x h W.guide).star).congr (fun t => ?_))
  simp only [Pi.star_apply, tallying,wakes,average_turn (R:=W.wall (k t)) (C:=relay F β m W.guide (k t)) rfl (W.seals F β m _),Function.comp_apply]
lemma reflected (hs : Sound F β m) (x : Cyl D F) (X : W.stands D) (H : Neutral x) (p : W.Within D S) (hp : D⊆S) :
    0 ≤ f.amp S (W.wake p x * crowd hp x) := by
  apply ge_of_tendsto (world (W.wake p x * crowd hp x) h W.guide)
  filter_upwards [k.cofinal.eventually (W.tactical D X)] with t ht
  rw [tallying, issue_mul,respect,wakes]
  exact RP.reflected_positive (C:=relay F β m W.guide (k t)) rfl (W.seals ..) (half_le _) hs.hb (by rw [destination]; exact hs.positive _) _
    ((sided _).mp (locates (spanT (k t)) x _ ht)) (issue_inv H)
end Wall
end YM.QCD.Land
