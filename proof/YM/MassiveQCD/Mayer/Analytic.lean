import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic
/-! # Mayer logarithm in a Banach algebra.
 Use no implicit global convergence or `IsUnit` assumption on exceptional points. Formula
 agrees with power sums on norm aperture. Later for profits require `SEN` norm budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Analysis.Many
open Function Filter Topology NormedSpace ContinuousLinearMap FormalMultilinearSeries Set Metric
open scoped ENNReal NNReal BigOperators Classical
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] [Nontrivial A]
abbrev alternate (n:ℕ):ℝ:=(-1)^n
def coeffM :ℕ→ℝ
 | 0=> 0
 | n+1=> alternate n / (n+1:ℕ)
lemma pace (n:ℕ): ‖alternate n‖=1:=by simp [alternate]
lemma horizon (n:ℕ): ‖coeffM n‖ ≤ 1:=by
    cases n; exact norm_zero.trans_le zero_le_one
    unfold coeffM; rw [norm_div, pace]; next n=> rw [Real.norm_of_nonneg]; exact one_div_le_one_div_of_le zero_lt_one (by norm_cast; omega) |>.trans (by norm_num); positivity
noncomputable def logM {A: Type*}[NormedCommRing A][NormedAlgebra ℝ A]:A→A:=fun x=>∑' n,coeffM n • x^n
omit [NormOneClass A] in
lemma ringGeom (x:A) (h:‖x‖<1) : HasSum (fun n:ℕ=> alternate n • x^n) (Ring.inverse (1+x)):=by
    have hh:= hasFPowerSeriesOnBall_inverse_one_add ℝ A; simpa only [sub_self,zero_add, alternatingGeometricSeries,ofScalars_apply_eq] using hh.hasSum (show x ∈ Metric.eball 0 1 from by simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using h)
omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
lemma plusUnit {x:A}(h:‖x‖<1): IsUnit (1+x):=by
    rw [show (1:A)+x=1-(-x) from by abel]; exact (Units.oneSub (-x) ((by rw [norm_neg]; exact h))).isUnit -- signature
omit [CompleteSpace A] [Nontrivial A] in
lemma logs {x:A}(h:‖x‖<1) : Summable fun n=> ‖coeffM n • x^n‖:= (summable_geometric_of_lt_one (norm_nonneg _) h).of_nonneg_of_le (fun _=> norm_nonneg _) (fun n=>by rw [norm_smul]; exact (mul_le_mul (horizon _) (norm_pow_le _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
lemma power (A : Type*) [NormedCommRing A][NormedAlgebra ℝ A][CompleteSpace A][NormOneClass A][Nontrivial A] : HasFPowerSeriesOnBall (logM (A:=A)) (ofScalars A coeffM) 0 1:=by
    refine ⟨?_,by norm_num,fun {i} hi=>?_⟩
    · suffices (↑(1:ℝ≥0):ℝ≥0∞) ≤ _ from (by simpa using this); apply le_radius_of_bound (ofScalars A coeffM) 1; intro n; rw [ofScalars_norm]; simpa using horizon n
    simp only [zero_add, ofScalars_apply_eq]; apply Summable.hasSum; apply Summable.of_norm; exact logs (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hi)
lemma cont_log (x:A)(h:‖x‖<1) : AnalyticAt ℝ logM x:= (power A).analyticAt_of_mem (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using h)
noncomputable def revBasis (A : Type*) [NormedCommRing A] [NormedAlgebra ℝ A] (u:A) : A →L[ℝ] A:= (ContinuousLinearMap.mul ℝ A) u
omit [CompleteSpace A] [NormOneClass A] [Nontrivial A] in
lemma swing (n:ℕ)(x:A): HasFDerivAt (fun y:A=>coeffM (n+1) • y^(n+1)) (revBasis A (alternate n • x^n)) x:=by
    apply (hasFDerivAt_pow (x:=x) (𝕜:=ℝ) (n+1)).const_smul (coeffM (n+1)) |>.congr_fderiv -- want L smul
    ext v; change coeffM (n+1) • (((n+1) • x^(n+1-1))*v)=(alternate n • x^n)*v; rw [Nat.add_sub_cancel,← Nat.cast_smul_eq_nsmul ℝ, Algebra.smul_mul_assoc, smul_smul,Algebra.smul_mul_assoc,coeffM]; rw [div_mul_cancel₀ _ (by positivity)] -- ambiguous mul_assoc
set_option maxHeartbeats 180000 in
lemma dlogM {x:A}(h:‖x‖<1): HasFDerivAt logM (revBasis A (Ring.inverse (1+x))) x:=by
    let a:= (1+‖x‖)/2; let p(n:ℕ):=‖ContinuousLinearMap.mul ℝ A‖*a^n; have hr :‖x‖<a:=by unfold a; linarith
    let S:=ball (0:A) a; have hc:S∈𝓝 x:= isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hr)
    have ha : a<1:=by unfold a; linarith
    have h₀:0 < a := (norm_nonneg _).trans_lt hr
    have hg : Summable p := (summable_geometric_of_lt_one h₀.le ha).mul_left _
    let f(n:ℕ)(x:A):= coeffM (n+1) • x^(n+1)
    let G:= ContinuousLinearMap.mul ℝ A
    let D(n:ℕ)(x:A):= G (alternate n • x^n)
    have hf(n y)(_hy:y∈S): HasFDerivAt (f n) (D n y) y:=swing n y
    have hD(n y)(hy:y∈S): ‖D n y‖≤ p n:=by
       apply ((ContinuousLinearMap.mul ℝ A).le_opNorm _).trans; rw [norm_smul,pace,one_mul]; exact mul_le_mul_of_nonneg_left ((norm_pow_le y n).trans (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hy).le _)) (norm_nonneg _)
    have hs : Summable (fun n=>f n x):= (((summable_nat_add_iff (f:=fun n:ℕ => coeffM n • x^n) 1).2 (logs h).of_norm))
    have hK:= hasFDerivAt_tsum_of_isPreconnected hg isOpen_ball (convex_ball (0:A) a |>.isPreconnected) hf hD (mem_ball_zero_iff.mpr hr) hs (mem_ball_zero_iff.mpr hr)
    have hz: (∑' n,D n x)=revBasis A (Ring.inverse (1+x)):= (G.hasSum (ringGeom x h)).tsum_eq
    rw [hz] at hK; apply hK.congr_of_eventuallyEq; filter_upwards [hc] with y hy; dsimp only [f]; have hh:= ((logs (x:=y) ((mem_ball_zero_iff.mp hy).trans ha)).of_norm).sum_add_tsum_nat_add 1; simpa only [Finset.sum_range_one, coeffM, zero_smul,zero_add, logM] using hh.symm

omit [CompleteSpace A] [NormOneClass A] [Nontrivial A] in
@[simp] lemma log_zero : logM (0:A)=0:=by
    unfold logM; rw [← ofScalars_sum_eq coeffM (0:A),ofScalarsSum_zero]; exact zero_smul ..
-- Exponential available in Banach algebra
variable [NormedAlgebra ℚ A]
lemma soothe (x:A) (h: ‖x‖<1) : exp (logM x) = 1+x:=by
    let f (x:A):=exp (-logM x)*(1+x)
    have he (x:A) (h:‖x‖<1): HasFDerivAt f (0: A→L[ℝ]A) x:=by
        let X:=exp (-logM x); let y:=1+x
        have hh: X*y* (Ring.inverse y)=X:=by rw [mul_assoc,Ring.mul_inverse_cancel y (plusUnit h),mul_one]
        have hg:= HasFDerivAt.mul ((hasFDerivAt_exp (𝕂:=ℝ) (x:=-logM x)).comp x (dlogM h).neg) ((hasFDerivAt_const (𝕜:=ℝ) (1:A) x).add (hasFDerivAt_id (𝕜:=ℝ) x))
        apply hg.congr_fderiv; ext v; change (X*((0 : A)+v)+y*(X*(-((Ring.inverse y)*v)))) = 0
        rw [zero_add,mul_neg,mul_neg]; have hm:= congr_arg (· * v) hh; linear_combination (norm := ring_nf) -hm
    have hp := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f:=f) (s:=Metric.ball (0:A) 1) (C:=0) (fun x hx => (he x (mem_ball_zero_iff.mp hx)).hasFDerivWithinAt) (fun x hx=>norm_zero.le) (convex_ball _ _) (show (0:A)∈Metric.ball 0 1 by simp) (mem_ball_zero_iff.mpr h)
    have hm : f x=f 0:=sub_eq_zero.mp (norm_le_zero_iff.mp (hp.trans_eq (zero_mul _)))
    have hv : f 0=1:=by simp [f]
    have hV:=congr_arg (exp (logM x)*·) (hm.trans hv); unfold f at hV; rw [← mul_assoc,← exp_add,add_neg_cancel, exp_zero,one_mul,mul_one] at hV; exact hV.symm
end YM.MassiveQCD.Analysis.Many
#print axioms YM.MassiveQCD.Analysis.Many.soothe
