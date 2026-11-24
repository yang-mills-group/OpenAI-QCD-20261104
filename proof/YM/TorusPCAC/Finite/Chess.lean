import YM.TorusPCAC.Finite.Reflection
import YM.Cells.Chess

/-!
# Checker saturation: chess inequality for unnormalized assignments

By assignment we consider labels in each tile and a price F on the entire
array (F nonnegative). With the seam Cauchy inequality on every split,
a chessboard estimate on any array of those labels. `F=0` is allowed
anywhere. This formulation of the library proof from `YM.Cells.Chess`
works for our vacuum value too, which will at first only be known
nonnegative. No new symmetry on masses/determinants or claim yet on which
arrays of probes (especially odd probes) have the seam properties.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Finite.Chess
open Lattice Cells Cells.Tiling Wilson MeasureTheory Function Finset Filter
open scoped Topology BigOperators

variable {n : Side} {α : Type*}

structure Condition (T : Tiling n) (F : (T.Cell → α) → ℝ) : Prop where
  nonneg (x) : 0 ≤ F x
  fold (p a) (x y : T.Cell → α) : F (T.assign p a x y)^2 ≤ F (T.assign p a x x) * F (T.assign p a y y)

variable {T : Tiling n} {F : (T.Cell → α) → ℝ}

open scoped Classical in
theorem pivot [Fintype α] [Nonempty α] (h : Condition T F) :
    ∃ c : α, ∀ f, F f ≤ F (fun _ => c) := by
  obtain ⟨B,-,hB⟩ := Finset.exists_max_image Finset.univ F Finset.univ_nonempty
  let Q f := F f = F B
  have hx : T.Reflects Q := by
    intro p a f hf
    let g x := f (T.mate p a x)
    have he := h.fold p a f g
    rw [show T.assign p a f g=f by funext i; unfold Tiling.assign; split; rfl; simp [g],
      show F f=F B from hf] at he
    let X := F B
    have hz : 0 ≤ X := h.nonneg B
    have hp := h.nonneg (T.assign p a f f)
    apply le_antisymm (hB _ (mem_univ _))
    rcases hz.eq_or_lt with hh|hh
    · exact hh.symm.le.trans hp
    exact le_of_mul_le_mul_right ((sq X) ▸ he.trans (mul_le_mul_of_nonneg_left (hB _ (mem_univ _)) hp)) hh
  obtain ⟨c,hc⟩ := T.existence Q hx B rfl
  exact ⟨c,fun i => (hB i (mem_univ _)).trans_eq (show F (fun _ => c) = F B from hc).symm⟩

theorem synced (p : T.Cell) (a : Axis) (f : T.Cell → ℝ) :
    ∏ i ∈ T.minusCells p a, f i = ∏ i ∈ T.plusCells p a, f (T.mate p a i) := by
  apply Complex.ofReal_injective; push_cast; exact T.switched ..

theorem scatter (p : T.Cell) (a : Axis) (f g : T.Cell → α) (R : α → ℝ) :
    ∏ i, R (T.assign p a f g i) = (∏ i ∈ T.plusCells p a, R (f i)) *
      ∏ i ∈ T.plusCells p a, R (g i) := by
  rw [T.cuts p a, prod_union (T.splitDisjoint p a),synced]; congr 1
  · exact prod_congr rfl fun i h => by rw [Tiling.assign, if_pos h]
  apply prod_congr rfl; intro i hi
  rw [Tiling.assign, if_neg ?_,T.mate_invol]; intro hv
  exact ((T.negative ..).mp ((T.cycles ..).mp hv)) hi

theorem scale (h : Condition T F) (R : α → ℝ) (hR : ∀ i, 0 ≤ R i) : Condition T
    (fun v => (∏ i, R (v i))*F v) := by
  constructor; · intro v; exact mul_nonneg (prod_nonneg (fun _ _ => hR _)) (h.nonneg v)
  intro p a v w
  let f := T.assign p a v v; let g := T.assign p a w w; let u := T.assign p a v w
  let X := ∏ i ∈ T.plusCells p a, R (v i); let Y := ∏ i ∈ T.plusCells p a, R (w i)
  simp_rw [scatter, mul_pow]; change (X^2*Y^2)*(F u)^2 ≤ X*X*F f*(Y*Y*F g)
  exact (mul_le_mul_of_nonneg_left (h.fold p a v w) (show 0 ≤ X^2*Y^2 by positivity)).trans_eq (by ring)

def price (x : α) (F : (T.Cell→α) → ℝ) := (F (fun _ => x)) ^ ((Fintype.card T.Cell : ℝ)⁻¹)

lemma powered (x : α) (h : Condition T F) : (price (T:=T) x F)^(Fintype.card T.Cell)=F (fun _ => x) := by
  unfold price; rw [← Real.rpow_natCast,← Real.rpow_mul (h.nonneg _),inv_mul_cancel₀ (by positivity),Real.rpow_one]

lemma price_nonneg (x : α) (h : Condition T F) : 0 ≤ price (T:=T) x F := Real.rpow_nonneg (h.nonneg _) _

private theorem chess_finite [Fintype α] [Nonempty α] (h : Condition T F) (v : T.Cell → α) :
    F v ≤ ∏ i, price (T:=T) (v i) F := by
  have he (ε : ℝ) (hε : 0 < ε) : F v ≤ ∏ i, (price (T:=T) (v i) F+ε) := by
    let Q := fun x => price (T:=T) x F
    let R := fun i => (Q i+ε)⁻¹
    have hp x : 0 < Q x+ε := add_pos_of_nonneg_of_pos (price_nonneg x h) hε
    have hh i : 0 < R i := inv_pos.mpr (hp i)
    obtain ⟨x,hx⟩ := pivot (scale h R (fun i => (hh i).le)); specialize hx v
    dsimp only at hx
    have hK : (∏ i : T.Cell, R x) * F (fun _ => x) ≤ 1 := by
      rw [prod_const,card_univ, ← powered x h, ← mul_pow]
      apply pow_le_one₀ (mul_nonneg (hh x).le (price_nonneg x h))
      rw [show R x = (Q x+ε)⁻¹ from rfl, inv_mul_le_iff₀ (hp x), mul_one]
      exact (lt_add_of_pos_right _ hε).le
    have hy := le_trans hx hK; dsimp only [R] at hy
    rw [prod_inv_distrib, inv_mul_le_iff₀ (prod_pos (fun i _ => hp (v i))), mul_one] at hy
    exact hy
  have hx : Tendsto (fun ε : ℝ => ∏ i, (price (T:=T) (v i) F+ε)) (𝓝[>] 0)
      (𝓝 (∏ i, price (T:=T) (v i) F)) := by
    have ht : Continuous (fun ε : ℝ => ∏ i, (price (T:=T) (v i) F+ε)) := by fun_prop
    simpa [ContinuousWithinAt] using ht.continuousAt.continuousWithinAt (x:=0) (s:=Set.Ioi 0)
  exact ge_of_tendsto hx ((show ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε from self_mem_nhdsWithin).mono fun ε h => he ε h)

/-- Arbitrary tile calls and chessboard powers. -/
theorem support_estimate (h : Condition T F) (v : T.Cell → α) :
    F v ≤ ∏ i, price (T:=T) (v i) F := by
  let G f := F (v ∘ f)
  have he : Condition T G := by
    constructor; · intro x; exact h.nonneg _
    intro s i a b
    have ht (p q : T.Cell → T.Cell) : T.assign s i (v ∘ p) (v ∘ q) = v ∘ T.assign s i p q := by
      funext x; unfold Tiling.assign; by_cases hh : x∈T.plusCells s i <;> simp only [hh,↓reduceIte,comp_apply]
    simpa only [ht] using h.fold s i (v ∘ a) (v ∘ b)
  exact chess_finite he id
end YM.TorusPCAC.Finite.Chess
