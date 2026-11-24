import YM.Next.ROTATIONS.Cove
import YM.Gust.Cav.OMass
import YM.Gust.Cav.OThaw
/- Variant of YM.Next.ROTATIONS.Cove, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {L : Register G} {S : Table L} {d : Axis} (V : Chamber S d)
lemma balanced (B A : Weight L) (f : ℕ→E4→ℂ) (hf : ∀ᶠ n in atTop,fits V B A (f n)) (a b : ℝ)
    (x y : ℕ→E4 → ℝ) (hx : ∀ᶠ n in atTop,Integrable (x n) (ν V B)) (hy : ∀ᶠ n in atTop, Integrable (y n) (ν V A))
    (ha : Budget a (fun n => integral (ν V B) (x n))) (hb : Budget b (fun n => integral (ν V A) (y n)))
    (hp : ∀ᶠ n in atTop, ∀ p : E4, 0≤p d → 0≤x n p ∧ 0≤y n p ∧ ‖f n p‖^2 ≤ x n p*y n p) :
    Budget ((a+b)/2) (fun n => cross V B A (f n)) := by
  let t := (b-a)/2
  apply ((((budget_fuel t).prod ha).rise (le_of_eq (by unfold t; ring))).add ((hb.prod (budget_inv t)).rise (le_of_eq (by unfold t; ring)))).priced
  filter_upwards [hf,hx,hy,hp] with n hn hx hy hp
  simpa only [div_eq_mul_inv] using cross_le V B A (f n) hn (x n) (y n) hx hy hp (fuel t n) (fuel_pos ..)
lemma balanced_mul (B A : Weight L) (f : ℕ→E4→ℂ) (hf : ∀ᶠ n in atTop,fits V B A (f n)) (a b : ℝ)
    (x y : ℕ→E4 → ℝ) (hx : ∀ n,Integrable (x n) (ν V B)) (hy : ∀ n, Integrable (y n) (ν V A))
    (ha : Budget a (fun n => integral (ν V B) (x n))) (hb : Budget b (fun n => integral (ν V A) (y n))) (t M : ℝ) (hM : 0≤ M)
    (hp : ∀ n, ∀ p : E4, 0≤p d → 0≤x n p ∧ 0≤y n p ∧ ‖f n p‖^2 ≤ (M*fuel t n)^2*(x n p*y n p)) :
    Budget (t+(a+b)/2) (fun n => cross V B A (f n)) := by
  let T (f : ℕ→E4→ℝ) := fun n p => (M*fuel t n)*f n p
  have hI (f : ℕ→E4→ℝ) (μ : Measure E4) (a) (h : Budget a (fun n => integral μ (f n))) :
      Budget (t+a) (fun n => integral μ (T f n)) := by unfold T; simp_rw [integral_const_mul]; exact ((budget_fuel t).times M).prod h
  refine (balanced V B A f hf (t+a) (t+b) (T x) (T y) (.of_forall fun n => (hx n).const_mul _) (.of_forall fun n => (hy n).const_mul _) (hI _ _ _ ha) (hI _ _ _ hb)
    (.of_forall fun n p he => ?_)).rise (le_of_eq (by ring))
  obtain ⟨hr,hq,hl⟩ := hp n p he
  unfold T; exact ⟨mul_nonneg (mul_nonneg hM (fuel_pos ..).le) hr,mul_nonneg (mul_nonneg hM (fuel_pos ..).le) hq,hl.trans_eq (by ring)⟩
private lemma ice_one (t u : ℝ) (ht : 0≤t) (hu : 0<u) : Real.exp (-(t/u)) ≤ u*(t+u)⁻¹ := by
  rw [Real.exp_neg]; apply le_trans (inv_anti₀ (show 0<t/u+1 from by positivity) (Real.add_one_le_exp (t/u))); apply le_of_eq; field_simp
private lemma ice_two (t u v : ℝ) (ht : 0≤t) (hu : 0<u) (hv : u≤v) : Real.exp (-(t/u)) ≤ 4*(v*(t+v)⁻¹)^2 := by
  have hw : 0<v := hu.trans_le hv
  apply le_trans (Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_left ht hu hv)))
  rw [show -(t/v)=-(t/(2*v))+ -(t/(2*v)) by ring,Real.exp_add,← sq]
  have hx : Real.exp (-(t/(2*v))) ≤ 2*(v*(t+v)⁻¹) := (ice_one _ _ ht (mul_pos (by norm_num) hw)).trans (by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith)) (by positivity))
  exact (pow_le_pow_left₀ (Real.exp_pos _).le hx 2).trans_eq (by ring)
end YM.Spiral.Outer

