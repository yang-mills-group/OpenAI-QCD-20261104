import YM.Planned.PRIMARY_INTEGRAL_295.Bijets
import YM.QCD.Flume.Fonts

/-! # Spin full polynomial-response exact; AP critical signs still kept per covariant call. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Function Filter Work.F08 Function Set Lattice Laurent Bloch Exterior RG Precision Next.Free Place
open scoped Topology BigOperators ContDiff ComplexConjugate Matrix.Norms.Frobenius
variable {L : Side} {j t : ℕ}
lemma complex_income {σ C : ℝ} (hσ : 0<σ) {q : Cover→ℂ} (hq : Width σ C q) (n : ℕ) :
    SumBudget (fun i : Cover => ‖q i‖ * liftCost n i) (widthCost σ n*C) := by
  let g (x : Cover) := Real.exp (σ*size x)*‖q x‖
  let p := widthCost σ n
  have hp : 0 ≤ p := zero_le_one.trans (widthCost_ge hσ n)
  have he : SumBudget (fun i => p*g i) (p*C) := ⟨fun i => mul_nonneg hp (hq.1 _),hq.2.1.mul_left _,by
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hq.2.2 hp⟩
  apply budget_minor he (fun _ => mul_nonneg (norm_nonneg _) (liftCost_pos ..)); intro i
  rw [mul_comm ‖q i‖]; refine (mul_le_mul_of_nonneg_right (widthBill σ hσ n _ (Nat.cast_nonneg (size i))) (norm_nonneg _)).trans_eq ?_
  exact mul_assoc ..

private def spinner (w : RouteProbe) (a : E4) (q : Cover → ℂ) (n : ℕ) (z : Cover) (t : ℝ) : ℂ :=
  let r : ℝ := w (a+seat z)
  (r*Complex.I)^n * tune r t * (q z:ℂ)

private lemma spinner_norm (w : RouteProbe) (a : E4) (q : Cover → ℂ) (n : ℕ) (z : Cover) (t : ℝ) :
    ‖spinner w a q n z t‖ = ‖q z‖ * ‖w (a+seat z)‖^n := by
  unfold spinner; simp only [Complex.norm_pow,norm_mul,tune_norm,Complex.norm_I, Complex.norm_real,mul_one]; exact mul_comm ..

private lemma spinner_sums (w : RouteProbe) (a : E4) (n : ℕ) {q : Cover → ℂ} {σ C : ℝ}
    (hσ : 0<σ) (h : Width σ C q) (t : ℝ) : Summable (fun z => ‖spinner w a q n z t‖) := by
  have he := complex_income hσ h n
  let p := 1 + ‖w‖ * (1+‖a‖)
  have hp (z : Cover) : ‖w (a+seat z)‖ ≤ p*(1+size z) := by
    apply (w.le_opNorm _).trans
    have he := add_le_add_right (shade_seat z) ‖a‖
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans he) (norm_nonneg _)).trans
    unfold p; nlinarith [norm_nonneg w,norm_nonneg a,Nat.cast_nonneg (α:=ℝ) (size z),mul_nonneg (mul_nonneg (norm_nonneg w) (norm_nonneg a)) (Nat.cast_nonneg (α:=ℝ) (size z))]
  apply (he.2.1.mul_left (p^n)).of_nonneg_of_le (fun _ => norm_nonneg _); intro i
  rw [spinner_norm]; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hp i) n) (norm_nonneg _)).trans_eq
  unfold liftCost; rw [mul_pow,mul_left_comm]

def ruckAt (w : RouteProbe) (a : E4) (q : Cover → ℂ) (t : ℝ) := ∑' z, tune (w (a+seat z)) t * (q z:ℂ)

lemma ruck_lift (w : RouteProbe) (a : E4) (q : Cover → ℂ) (t : ℝ) :
    ruckAt w a q t=tune (w a) t * Laurent.read q (ray w t) := by
  unfold ruckAt Laurent.read; rw [← tsum_mul_left]; refine tsum_congr fun i => ?_
  rw [through_mode,map_add,tune_add,mul_assoc]; rfl

private lemma ruck_side (w : RouteProbe) (a : E4) (n : ℕ) {q : Cover → ℂ} {σ C : ℝ} (hσ : 0 < σ)
    (h : Width σ C q) : iteratedDeriv n (ruckAt w a q) =(fun t => ∑' z, spinner w a q n z t) := by
  classical
  induction n with
  | zero => funext t; simp [ruckAt, spinner]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]; funext t
    let u := spinner w a q
    have hd (z s) : HasDerivAt (u n z) (u (n+1) z s) s := by
      let r := w (a+seat z)
      unfold u spinner
      apply (((tune_derivative r s).const_mul _).mul_const _).congr_deriv
      unfold r; dsimp only; ring
    exact (hasDerivAt_tsum (spinner_sums w a (n+1) hσ h 0) hd
      (fun z s => le_of_eq (by unfold u;rw [spinner_norm,spinner_norm]))
      ((spinner_sums w a n hσ h 0).of_norm) t).deriv

/-- The actual (unnormalized) derivative order n, in initial-vertex
coordinates, translated by ANY continuous origin a. -/
lemma march_points (w : RouteProbe) (a : E4) (n : ℕ) {q : Cover → ℂ} {σ C : ℝ} (hσ : 0<σ) (h : Width σ C q) :
    iteratedDeriv n (ruckAt w a q) 0 = Complex.I^n * ∑' z:Cover, (((w (a+seat z))^n:ℝ):ℂ)*q z := by
  rw [ruck_side w a n hσ h, ← tsum_mul_left]
  refine tsum_congr fun i => ?_; unfold spinner; simp only [tune_one, mul_one, Complex.ofReal_mul, Complex.ofReal_pow]; ring

end YM.Planned.PrimaryIntegral295.Carrier