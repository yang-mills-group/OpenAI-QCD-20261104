import YM.QCD.Nola.Ac
import YM.Push.ABSOLUTE_SUMS.Weigh

/-!
# Trees with exponential cardinal only. Fine hopping addresses needn't form nearest-neighbour stencils. This version keeps exponent reserve in per-incident *leg* counting. Adaptation of Yang gauge trees.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Trees
open Lattice Finset RG Animals
open scoped Topology BigOperators Classical

variable {n : Side} {ι : Type*} (X : ι → Support n)

/-- Set coefficient weight, also applies to winding supports. -/
def currencyCard (a : ℝ) (Y : Support n) := Real.exp (a * Finset.card Y)

def overlapWeightCard (w : ι → ℝ) (a : ℝ) (Y : Support n) (i : ι) :=
    if Ac.meets X i Y then w i * currencyCard a (X i) else 0

def stretchCard (γ δ : ℝ) := (1:ℝ) * γ / δ

def degreePriceCard (γ δ : ℝ) := 4 * stretchCard γ δ

def fanPriceCard (δ : ℝ) (Y : Support n) : ℝ := max (δ * Finset.card Y) 1

lemma overlap_sumCard {w : ι → ℝ} {a γ : ℝ} (hh : Ac.HitCard X w a γ) (Y : Support n) (D : Finset ι) :
    ∑ i ∈ D, overlapWeightCard X w a Y i ≤ Y.card*γ := by
  simpa only [Ac.buds,Finset.sum_filter,currencyCard,overlapWeightCard] using Ac.demandCard X hh Y D

lemma overlap_nonnegCard (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : ℝ) (Y : Support n) (i : ι) :
    0 ≤ overlapWeightCard X w a Y i := by
  unfold overlapWeightCard; split
  · exact mul_nonneg (hw _) (Real.exp_pos _).le
  exact le_rfl

lemma stretch_posCard {γ δ : ℝ} (hk : 0 < γ) (hd : 0 < δ) : 0 < stretchCard γ δ := by
  unfold stretchCard; positivity

lemma fanPrice_posCard (Y : Support n) (δ : ℝ) : 0 < fanPriceCard δ Y := by unfold fanPriceCard; positivity

private lemma pays_fanCard (Y : Support n) {δ : ℝ} (hd : 0 < δ) (k : ℕ) :
    fanPriceCard δ Y ^ k ≤ (k.factorial:ℝ) * currencyCard δ Y := by
  let x : ℝ := δ * Finset.card Y
  have hx : 0 ≤ x := by unfold x; positivity
  have he : 1 ≤ (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  change (max x 1)^k ≤ _ * Real.exp x
  rcases le_total 1 x with h|h
  · rw [max_eq_left h]
    have hk := (div_le_iff₀ (show 0 < (k.factorial:ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp _ hx k)
    rwa [mul_comm]
  rw [max_eq_right h,one_pow]
  exact he.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp hx))

/-- Weight for one numbered forestCard, with parent-map and full labels. -/
def forestWeightCard {α : Type*} [Fintype α] (w : ι → ℝ) (a : ℝ)
    (Y : Support n) (p : α → Option α) (z : α → ι) : ℝ :=
    if Sprouts X Y p z then (∏ i, (w (z i)*currencyCard a (X (z i)))) / (Fintype.card α).factorial else 0

lemma forest_nonnegCard {α : Type*} [Fintype α] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℝ)
    (Y : Support n) (p : α → Option α) (z : α → ι) :
    0 ≤ forestWeightCard X w a Y p z := by
  unfold forestWeightCard; split
  · exact div_nonneg (prod_nonneg fun i _ => mul_nonneg (hw _) (Real.exp_pos _).le) (by positivity)
  exact le_rfl

private lemma overlap_eqCard {α : Type*} [Fintype α] (w : ι → ℝ) (a : ℝ)
    (Y : Support n) (p : α → Option α) (z : α → ι) (h : Ranked p) :
    forestWeightCard X w a Y p z = (∏ i, overlapWeightCard X w a (installed X Y z (p i)) (z i)) /
      (Fintype.card α).factorial := by
  unfold forestWeightCard; split
  next he =>
    congr 1
    exact prod_congr rfl (fun i _ => (if_pos (he.2 i)).symm)
  next he =>
    simp only [Sprouts,h,true_and,not_forall] at he
    obtain ⟨i,hi⟩ := he
    rw [prod_eq_zero (mem_univ i) (show overlapWeightCard X w a (installed X Y z (p i)) (z i) = 0 from
      if_neg hi), zero_div]

private lemma prod_fanPriceCard {α : Type*} [Fintype α] [DecidableEq α] {δ : ℝ} (hd : 0 < δ)
    (Y : Support n) (p : α → Option α) (z : α → ι) :
    (∏ i, fanPriceCard δ (installed X Y z (p i))) ≤ (fanout p:ℝ) * (currencyCard δ Y *
      ∏ i : α, currencyCard δ (X (z i))) := by
  let c i := installed X Y z i
  calc
    _ = ∏ i : Option α, fanPriceCard δ (c i) ^ children p i := by
      have he := prod_fiberwise univ p (fun j => fanPriceCard δ (c (p j)))
      apply he.symm.trans
      apply prod_congr rfl; intro i _
      calc
        _ = ∏ _j ∈ univ with p _j=i, fanPriceCard δ (c i) := prod_congr rfl fun j hj => by
          rw [(mem_filter.mp hj).2]
        _ = _ := Finset.prod_const _
    _ ≤ ∏ i : Option α, ((children p i).factorial:ℝ) * currencyCard δ (c i) :=
      prod_le_prod (fun i _ => pow_nonneg (fanPrice_posCard (c i) δ).le _) fun i _ => pays_fanCard _ hd _
    _ = _ := by
      rw [prod_mul_distrib,fanout,Nat.cast_prod,Fintype.prod_option (fun i => currencyCard δ (c i))]; rfl

-- Transition kernels for the proof: with extra exponent and normalized.
private def kernelCard (w : ι → ℝ) (a γ δ : ℝ) (Y : Support n) (i : ι) :=
    overlapWeightCard X w (a+δ) Y i / (stretchCard γ δ * fanPriceCard δ Y)

private lemma kernel_sumCard {w : ι → ℝ} {a γ δ : ℝ} (hg : 0 < γ) (hd : 0 < δ)
    (hh : Ac.HitCard X w (a+δ) γ) (Y : Support n) (D : Finset ι) :
    ∑ i ∈ D, kernelCard X w a γ δ Y i ≤ 1 := by
  have ho := stretch_posCard hg hd; have hm := fanPrice_posCard Y δ
  let c : ℝ := Finset.card Y
  have hy : (Y.card:ℝ) ≤ (1:ℝ) * c := by
    rw [one_mul]
  unfold kernelCard; rw [← sum_div,div_le_one (by positivity)]
  apply (overlap_sumCard X hh Y D).trans
  calc
    _ ≤ ((1:ℝ) * c)*γ := mul_le_mul_of_nonneg_right hy hg.le
    _ = stretchCard γ δ * (δ * c) := by unfold stretchCard; field_simp
    _ ≤ stretchCard γ δ * fanPriceCard δ Y := mul_le_mul_of_nonneg_left (le_max_left ..) ho.le

private lemma kernel_posCard {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {γ δ : ℝ} (hg : 0 < γ) (hd : 0 < δ)
    (a : ℝ) (Y : Support n) (i : ι) : 0 ≤ kernelCard X w a γ δ Y i :=
    div_nonneg (overlap_nonnegCard X w hw _ Y i) (mul_nonneg (stretch_posCard hg hd).le (fanPrice_posCard _ _).le)

private lemma buyCard {α : Type*} [Fintype α] [DecidableEq α] {δ γ : ℝ} (hd : 0 < δ) (hg : 0 < γ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (Y : Support n) (p : α → Option α) (z : α → ι) (a : ℝ) :
    let G := installed X Y z
    let O (i : α) := overlapWeightCard X w a (G (p i)) (z i)
    let K (i : α) := kernelCard X w a γ δ (G (p i)) (z i)
    (∏ i, O i) ≤ currencyCard δ Y * (stretchCard γ δ)^Fintype.card α * fanout p * ∏ i, K i := by
  intro G O K
  let t := stretchCard γ δ
  have ht : 0 < t := stretch_posCard hg hd
  let u i := currencyCard δ (X (z i))
  have hx i : 0 < u i := Real.exp_pos _
  have hh i : 0 ≤ K i := kernel_posCard X hw hg hd a _ _
  have eq (i : α) : O i * u i = t * fanPriceCard δ (G (p i)) * K i := by
    unfold O K kernelCard overlapWeightCard
    split
    next h =>
      have he : currencyCard (a+δ) (X (z i)) = currencyCard a (X (z i)) * u i := by
        rw [currencyCard,add_mul,Real.exp_add]; rfl
      change _ = t * _ * (_ * _ / (t*_))
      rw [he]; have hb := fanPrice_posCard (G (p i)) δ; field_simp
    next h => simp
  apply le_of_mul_le_mul_right (a:=∏ i, u i) ?_ (Finset.prod_pos (fun i _ => hx i))
  calc
    _ = ∏ i, t * fanPriceCard δ (G (p i)) * K i := by
      rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => eq i
    _ = (t^Fintype.card α * ∏ i, K i) * ∏ i, fanPriceCard δ (G (p i)) := by
      simp_rw [prod_mul_distrib,Finset.prod_const,card_univ]; ring
    _ ≤ (t^Fintype.card α * ∏ i, K i) * ((fanout p:ℝ) * (currencyCard δ Y * ∏ i, u i)) :=
      mul_le_mul_of_nonneg_left (prod_fanPriceCard X hd Y p z) (mul_nonneg (pow_nonneg ht.le _)
        (prod_nonneg fun i _ => hh i))
    _ = _ := by unfold t; ring

/-- Uniform at each finite D. This stepCard pays all child factorials. -/
theorem trees_affordCard (m : ℕ) (D : Finset ι) (Y : Support n) {γ δ a : ℝ} (hg : 0 < γ)
    (hd : 0 < δ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hh : Ac.HitCard X w (a+δ) γ) :
    ∑ p : Fin m → Option (Fin m), ∑ z : Fin m → D, forestWeightCard X w a Y p (fun i => (z i).val) ≤
      currencyCard δ Y * (degreePriceCard γ δ)^m := by
  let A := Fin m → Option (Fin m)
  let g p (z : Fin m → D) := forestWeightCard X w a Y p (fun i => (z i).val)
  let t := stretchCard γ δ
  let v := currencyCard δ Y
  let K := fun (Y : Support n) (i : D) => kernelCard X w a γ δ Y i.val
  let Z := fun i : D => X i.val
  have hi Y i : 0 ≤ K Y i := kernel_posCard X hw hg hd a _ _
  have hk Y : ∑ i:D, K Y i ≤ 1 := by
    rw [← sum_subtype D (p:=(· ∈ D)) (fun _ => Iff.rfl)
      (kernelCard X w a γ δ Y)]; exact kernel_sumCard X hg hd hh Y D
  have hv : 0 ≤ v := (Real.exp_pos _).le
  have ht : 0 < t := stretch_posCard hg hd
  have hm : 0 < (m.factorial:ℝ) := by positivity
  have he (p : A) : (∑ z, g p z) ≤ v * t^m * fanout p / m.factorial := by
    rw [le_div_iff₀ hm,sum_mul]; by_cases H : Ranked p
    · let q (z : Fin m → D) := ∏ i, K (installed Z Y z (p i)) (z i)
      calc
        _ ≤ ∑ z : Fin m → D, (v * t^m * fanout p) * q z := sum_le_sum fun z _ => by
          unfold g; rw [overlap_eqCard X w a Y p _ H,Fintype.card_fin,div_mul_cancel₀ _ hm.ne']
          simpa! only [Fintype.card_fin,q,v,t,K,Z,installed,Function.comp_def] using buyCard X hd hg hw Y p (fun i => (z i).val) a
        _ ≤ _ := by
          rw [← mul_sum]; apply mul_le_of_le_one_right (by positivity)
          exact substochastic Y Z K p H hi hk
    have hz z : g p z = 0 := by simp [g,forestWeightCard,Sprouts,H]
    simp_rw [hz,zero_mul,sum_const_zero]; positivity
  change ∑ p:A, ∑ z, g p z ≤ _
  calc
    _ ≤ ∑ p:A, v * t^m * fanout p / m.factorial := sum_le_sum fun p _ => he p
    _ = v*t^m*(∑ p:A, (fanout p:ℝ)) / m.factorial := by rw [mul_sum,sum_div]
    _ ≤ v*t^m*((4:ℝ)^m*m.factorial) / m.factorial := by
      gcongr
      exact_mod_cast parent_fanout m
    _ = _ := by unfold degreePriceCard; change _ = v*(4*t)^m; rw [mul_pow]; field_simp
end YM.Push.AbsoluteSums.Trees
