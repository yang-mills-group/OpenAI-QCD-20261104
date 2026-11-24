import YM.QCD.Nola.Forest
import YM.Push.ABSOLUTE_SUMS.Forest
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Trees
open Lattice Finset RG Relation
open scoped Topology BigOperators Classical
variable {ι : Type*} {n : Side} (X : ι → Support n)

/-- Sufficient smallness condition and convenient geometric rate `q`. -/
def ReadyCard (w : ι → ℝ) (a γ δ q : ℝ) : Prop :=
    0 < γ ∧ 0 < δ ∧ degreePriceCard γ δ ≤ q ∧ q < 1 ∧ (∀ i, 0 ≤ w i) ∧ Ac.HitCard X w (a+δ) γ

lemma ready_posCard {w : ι → ℝ} {a γ δ q : ℝ} (h : ReadyCard X w a γ δ q) : 0 < q := by
  rcases h with ⟨hg,hd,hq,-⟩
  unfold degreePriceCard at hq; have ht := stretch_posCard hg hd; linarith

def forestWCard (Y : Support n) (w : ι → ℝ) (a : ℝ) (z : Forest ι) :=
    forestWeightCard X w a Y z.2.1 z.2.2

def rootWCard (w u : ι → ℝ) (a : ℝ) (z : Root ι) :=
    let i := z.2.1
    -- u the (test-hit, marked or arbitrary paid) ROOT weight
    u i * currencyCard a (X i) * forestWCard X (X i) w a ⟨z.1,z.2.2⟩

lemma forest_atCard (Y : Support n) {w : ι → ℝ} {a γ δ q : ℝ}
    (h : ReadyCard X w a γ δ q) (m : ℕ) : SumBudget
      (fun z : ForestAt ι m => forestWCard X Y w a ⟨m,z⟩)
      (currencyCard δ Y * q^m) := by
  rcases h with ⟨hg,hd,hq,h1,hw,hh⟩
  apply budget_assignments (fun z : _ × (Fin m → ι) => forestWeightCard X w a Y z.1 z.2)
    (fun i => forest_nonnegCard X hw a Y i.1 i.2)
  intro D
  have hp : 0 ≤ degreePriceCard γ δ := mul_nonneg (by norm_num) (stretch_posCard hg hd).le
  exact (trees_affordCard X m D Y hg hd hw hh).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp hq _) (Real.exp_pos _).le)



lemma root_atCard {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : ReadyCard X w a γ δ q) (he : SumBudget (fun i => u i * currencyCard (a+δ) (X i)) b)
    (m : ℕ) : SumBudget (fun z : RootAt ι m => rootWCard X w u a ⟨m,z⟩) (b * q^m) := by
  rw [mul_comm b]
  refine budget_rows _ (fun i => q^m*(u i * currencyCard (a+δ) (X i))) (fun k => ?_)
    (budget_scale (pow_nonneg (ready_posCard X h).le m) he)
  have hx := budget_scale (show 0 ≤ u k * currencyCard a (X k) from
    mul_nonneg (hu k) (Real.exp_pos _).le) (forest_atCard X (X k) h m)
  apply budget_loosen hx
  unfold currencyCard; rw [add_mul,Real.exp_add]; apply le_of_eq; ring



section Cover
variable {α : Type*}

lemma forestW_nonnegCard (Y : Support n) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℝ)
    (z : Forest ι) : 0 ≤ forestWCard X Y w a z := forest_nonnegCard X hw a _ _ _

lemma rootW_nonnegCard {u w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) (a : ℝ)
    (z : Root ι) : 0 ≤ rootWCard X w u a z := mul_nonneg (mul_nonneg (hu _) (Real.exp_pos _).le)
      (forestW_nonnegCard X _ hw a _)







/-- HitCard x by the designated root. Logs that may be hit at ANY
vertex use this estimate over arbitrary numberings with their proper
factorial (the normalization here already allows for the root choice).
Supports w/o hits need their separate treatment. -/
lemma test_hitCard {w : ι → ℝ} {a γ δ q : ℝ} (h : ReadyCard X w a γ δ q) (x : Site n) :
    SumBudget (fun i => hit X w x i * currencyCard (a+δ) (X i)) γ := by
  convert h.2.2.2.2.2 x using 1
  ext i; by_cases he : x∈X i <;> simp [hit,currencyCard,he]


end Cover
end YM.Push.AbsoluteSums.Trees
