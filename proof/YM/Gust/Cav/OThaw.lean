import YM.Next.ROTATIONS.Thaw
import YM.Gust.Cav.OMass
/- Variant of YM.Next.ROTATIONS.Thaw, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace
private def val (f : Form) (k : ℕ) := SchwartzMap.seminorm ℝ k 0 f
private lemma ordinary (f : Form) (x K q : ℝ) (n : ℕ) (h : -K ≤ x) : ‖large (fuel x n) f q‖ ≤ val f 0*fuel K n := by
  rw [large_at,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (fuel_pos x n)).le,← fuel_neg,mul_comm (fuel ..)]
  exact mul_le_mul (f.norm_le_seminorm ℝ _) (fuel_le (by linarith) _) (fuel_pos ..).le (apply_nonneg _ _)
private lemma extraordinary (f : Form) (x K q : ℝ) (k n : ℕ) (h : -K ≤ x) (hp : fuel (1+x) n < |q|) :
    ‖large (fuel x n) f q‖ ≤ val f k * fuel (K-k) n := by
  rw [large_at,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (fuel_pos x n)).le,← fuel_neg]
  let r := q/fuel x n
  have hr : fuel 1 n ≤ ‖r‖ := by
    unfold r; rw [norm_div,Real.norm_of_nonneg (fuel_pos ..).le, le_div_iff₀ (fuel_pos ..),fuel_mul]; exact hp.le
  have ht : fuel k n * ‖f r‖ ≤ val f k := by
    rw [show fuel k n=fuel 1 n^k by rw [fuel_rate,one_mul]]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (fuel_pos ..).le hr k) (norm_nonneg _)).trans (f.norm_pow_mul_le_seminorm ℝ k r)
  have hl : ‖f r‖ ≤ val f k * fuel (-(k:ℝ)) n := by rw [fuel_neg,← div_eq_mul_inv, le_div_iff₀ (fuel_pos ..),mul_comm]; exact ht
  exact (mul_le_mul (fuel_le (by linarith : -x≤K) n) hl (norm_nonneg _) (fuel_pos ..).le).trans_eq (by rw [mul_left_comm,fuel_mul,← sub_eq_add_neg])
private lemma sells (d K M : ℝ) (hd : d<0) (hK : 0<K) : ∀ᶠ n : ℕ in atTop,
    (n:ℝ)*K + M ≤ fuel (-d) n := by
  have he : Tendsto (fun n : ℕ => n * (-d)) atTop atTop := tendsto_natCast_atTop_atTop.atTop_mul_const (neg_pos.mpr hd)
  filter_upwards [(Real.tendsto_exp_div_pow_atTop 1 |>.comp he).eventually (eventually_ge_atTop ((K+1)/(-d))),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop M),eventually_gt_atTop (0:ℕ)] with n hn hn' h
  change (K+1)/(-d) ≤ Real.exp _ / ((n:ℝ)*(-d))^1 at hn; simp only [pow_one] at hn
  have hh : 0 < (n:ℝ) := Nat.cast_pos.mpr h
  rw [le_div_iff₀ (mul_pos hh (neg_pos.mpr hd))] at hn
  rw [show (K+1)/(-d)*(n*(-d)) = n*(K+1) by field_simp [hd.ne]] at hn
  unfold fuel; change M≤(n:ℝ) at hn'; linarith
variable {G : Gauge} {L : Register G} {S : Table L}
open scoped Classical in
theorem ice (w : Axis→ℝ) (d : Axis) (V : Chamber S d) (H : S.Hierarchy) (B A : Weight L) (f : Panels)
    (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) (K : ℝ) (hw : ∀ i, -K ≤ w i) (hd : w d<0) (b : ℂ) (hb : ‖b‖=1)
    (y : ℝ) : Budget y (fun n => cross V B A ((cove w d n )ᶜ.indicator (answer d b (tracks w d n f)))) := by
  obtain ⟨u,hU,hV⟩ := ((descends d B).and (descends d A)).exists
  obtain ⟨a,ha⟩ := exists_ne d
  let t : ℝ := ↑(u+u:ℝ≥0)
  obtain ⟨M,hM,hX⟩ := farther w d f h K hw hd t (by exact NNReal.coe_nonneg _) y b hb
  unfold cross; refine Budget.times (budget_sum _ _ _ (fun j _ => Budget.times ?_ _)) _
  let p := mom d a 0 t
  let μ := ν V (combo B A j)
  apply ((((budget_fuel y).times M).prod (constant_budget (∫ x,p x ∂μ))).rise (le_of_eq (by ring))).priced
  filter_upwards [hX] with n hn
  change _ ≤ M*fuel y n * ∫ x, p x ∂μ
  rw [← integral_const_mul]; refine norm_integral_le_of_norm_le ((placed_moment V H _ a ha 0 u (meets_air _ _ _ hU hV j)).const_mul _) ?_
  filter_upwards [before V (combo B A j)] with q hq
  by_cases he : q∈cove w d n
  · rw [indicator_of_notMem (show q∉(cove w d n)ᶜ from not_not_intro he),norm_zero]; exact mul_nonneg (mul_nonneg hM (fuel_pos ..).le) (mom_nn ..)
  rw [indicator_of_mem (show q∈(cove w d n)ᶜ from he)]; simp only [p,mom,Nat.mul_zero,pow_zero,mul_one]
  exact hn q hq he
end YM.Spiral.Outer

