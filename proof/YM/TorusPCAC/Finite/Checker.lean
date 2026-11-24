import YM.TorusPCAC.Finite.Insert
import YM.TorusPCAC.Finite.Chess

/-!
# Checkerboard saturation: place the onsite probe pattern

Width one cells, using only link reflection positivity. Mass insertions
work evenly on every site (only their scalar tags vary), so use the parity
checker pattern without any Grassmann copy-orientation lemma about
non-scalar insertions. `width` gives both half-size and its certificate;
avoid ruling out incommensurate odd/even halves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Finite.Checker
open QCD QCD.Lat Lattice Wilson Cells.Tiling MeasureTheory Function Finset Filter
open scoped Topology BigOperators
variable {n : Side} {N : ℕ}

structure Width (n : Side) where
  half : Side
  even : n.val=2*half.val
  space : 2 ≤ half.val

namespace Width

variable (w : Width n)
abbrev tiles (w : Width n) : Cells.Tiling n := ⟨n,⟨1,by simp⟩,w.half,w.even,.link,0⟩
abbrev R (w : Width n) (p : Site n) (a : Axis) := w.tiles.bandCut p a

lemma pos (p : Site n) (a : Axis) : (w.R p a).pos=a := rfl
lemma half_wide (p : Site n) (a : Axis) : 2 ≤ (w.R p a).half.val := by
  change 2 ≤ (1*w.half : Side).val; rw [one_mul]; exact w.space
lemma begins (p : Site n) : w.tiles.starts p=p := by
  rw [Cells.Tiling.starts]
  change 0+_ = _; rw [zero_add]; change wrap n ((1:ℕ) • lift p) = p; rw [one_smul,wrap_lift]
lemma axis (p : Site n) (a : Axis) : (w.R p a).baseLine=p a := by
  change w.tiles.starts _ _=_; rw [w.begins]
lemma mates (p : Site n) (a : Axis) (i : Site n) : w.tiles.mate p a i=(w.R p a).reflect i := by
  ext j; by_cases h : j=a
  · subst j; rw [mate_here]; change _= (w.R p a).reflect i (w.R p a).pos; rw [Cells.Cut.reflect_here,w.axis,w.pos,show (w.R p a).kind.shift=1 from rfl]; simp
  rw [mate_off _ _ _ _ h, Cells.Cut.reflect_there _ _ h]
lemma positive_side (p : Site n) (a : Axis) (i : Site n) :
    i ∈ (w.R p a).sector ↔ i ∈ w.tiles.plusCells p a := by
  rw [Cells.Tiling.positive_side]
  change ((i _ - (w.R p a).baseLine).val : ℕ)<(w.R p a).half.val ↔ _
  rw [w.axis, show (w.R p a).half = w.half from one_mul _]; rfl

def keep (p : Site n) (a : Axis) (f : Site n → ℝ) (x : Site n) := if x∈w.tiles.plusCells p a then f x else 0
lemma lies (p : Site n) (a : Axis) (f) : support (w.keep p a f) ⊆ (w.R p a).sector := by
  intro x hx; rw [w.positive_side]; by_contra h; exact hx (if_neg h)
lemma assign (p : Site n) (a : Axis) (f g : Site n → ℝ) : w.tiles.assign p a f g =
    w.keep p a f+w.keep p a g ∘ (w.R p a).reflect := by
  funext x
  unfold Cells.Tiling.assign
  simp only [keep,Pi.add_apply,Function.comp_apply,← w.mates,
    w.tiles.cycles,w.tiles.negative]; split_ifs <;> first| rw [zero_add]| rw [add_zero]

lemma satisfies (B : Torus n N) (hb : 0 ≤ B.beta) : Chess.Condition w.tiles (Marker.price B) := by
  constructor; · intro v; exact norm_nonneg _
  intro p a f g; simp_rw [w.assign]
  exact Marker.split B _ _ _ rfl hb (w.half_wide p a) (w.lies ..) (w.lies ..)

/-- Bipartite even/odd site invariant. -/
def shade (i : Site n) : ZMod 2 := ∑ a, w.tiles.parity (i a)
def occupied : Finset (Site n) := univ.filter fun i => w.shade i=1

lemma opposite (a : Axis) (x : Site n) : w.shade (x+ step a)=w.shade x+1 := by
  unfold shade
  have he (b : Axis) : w.tiles.parity ((x+step a : Site n) b)=w.tiles.parity (x b)+w.tiles.parity ((step a : Site n) b) := w.tiles.parity_add ..
  simp_rw [he,Finset.sum_add_distrib]; congr 1
  rw [sum_eq_single a]; · simp
  · intro b _ h; simp [h]
  simp
lemma mem_hop (a : Axis) (x : Site n) : x+step a∈w.occupied ↔ x∈w.occupiedᶜ := by
  unfold occupied; simp only [mem_compl,mem_filter,mem_univ, true_and, opposite, add_eq_right]
  generalize w.shade x=v; have hh : v=0 ∨ v=1 := by fin_cases v <;> simp [ZMod]
  rcases hh with e|e <;> simp [e]
lemma equal : w.occupied.card = w.occupiedᶜ.card := Eq.symm (card_bij'
  (fun i _ => i+step 0) (fun i _ => i-step 0) (fun _ h => (w.mem_hop ..).mpr h)
  (fun i h => (w.mem_hop ..).mp (show i-step 0+step 0∈w.occupied by simpa using h))
  (by simp) (by simp))
lemma covers : Fintype.card (Site n) = w.occupied.card*2 := by
  have ho := w.occupied.card_le_univ; have he:= w.equal; rw [card_compl] at he; omega

/-- Price of the checker assignment in terms of the two extreme vacuum
prices. Keep this as a square inequality. -/
theorem checker (B : Torus n N) (hb : 0≤ B.beta) (f g : ℝ) :
    Marker.price B (fun i=> if i∈w.occupied then f else g) ^ 2 ≤
    Marker.price B (fun _=> f) * Marker.price B (fun _=>g) := by
  let P x := Chess.price (T:=w.tiles) x (Marker.price B)
  have h := Chess.support_estimate (w.satisfies B hb) (fun i => if i∈w.occupied then f else g)
  have hp : ∀ a,0 ≤ P a := fun a=> Chess.price_nonneg _ (w.satisfies B hb)
  let S : Finset (w.tiles.Cell):= w.occupied
  have he : ∏ i:w.tiles.Cell, P (if i∈ S then f else g)=P f^S.card * P g^S.card := by
    rw [show (fun i:w.tiles.Cell=> P (if i∈ S then f else g))=(fun i=> if i∈ S then P f else P g) from by ext i; split_ifs <;> rfl,prod_ite]
    rw [show (univ.filter fun x=> x∈ S)=S by ext; simp, show (univ.filter fun x=> x∉ S)=Sᶜ by ext; simp,prod_const,prod_const]
    rw [show Sᶜ.card=S.card from w.equal.symm]
  change _ ≤ ∏ i:w.tiles.Cell, P (if i∈ S then f else g) at h
  apply le_trans (pow_le_pow_left₀ (norm_nonneg _) h 2)
  have hu : Fintype.card w.tiles.Cell=S.card*2:=w.covers
  rw [he,mul_pow,← pow_mul, ← pow_mul, ← hu]; exact le_of_eq (congrArg₂ (·*·) (Chess.powered _ (w.satisfies B hb)) (Chess.powered _ (w.satisfies B hb)))
end Width
end YM.TorusPCAC.Finite.Checker
