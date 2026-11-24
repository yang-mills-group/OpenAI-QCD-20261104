import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Logarithmic change to Mayer coordinates
In a commutative Banach algebra, use the series-based chart. This preserves
finite-rank (anti-)linear symmetries even as a globally defined function
(not even continuous outside the disk). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Log
open Set Filter Function Metric NormedSpace FormalMultilinearSeries
open scoped Topology BigOperators ContDiff NNReal ENNReal
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A]
variable (x:A)
noncomputable def c (n:ℕ):ℝ:= -((-1)^n)/(n:ℝ)
noncomputable def log (x:A):A:= ofScalarsSum c x
noncomputable def rev (x:A):A:= ofScalarsSum (fun n:ℕ=> (-1:ℝ)^n) x
lemma log_eq : log x= ∑' n:ℕ,c n • x^n:= ofScalars_sum_eq ..
@[simp] lemma log_zero : log (0:A)=0:=by unfold log; rw [ofScalarsSum_zero]; simp [c]
lemma rev_eq : rev x=∑' n:ℕ,(-x)^n:=by
    unfold rev; rw [ofScalars_sum_eq]; apply tsum_congr; intro i; rw [← smul_pow,neg_one_smul]
lemma c_succ (n:ℕ): c (n+1)=(-1:ℝ)^n/(n+1):=by rw [c,Nat.cast_add_one,pow_succ]; ring
lemma priced (n:ℕ): ‖c n‖≤1:=by
    cases n
    · simp [c]
    next n=> rw [c_succ,norm_div,norm_pow,norm_neg,norm_one,one_pow,Real.norm_of_nonneg (by positivity)]; exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α:=ℝ) n]) (by positivity)
variable [NormOneClass A] [CompleteSpace A]
lemma basic {x:A} {f:ℕ→ℝ} (h:∀ i, ‖f i‖≤1) (hx:‖x‖<1) : AnalyticAt ℝ (ofScalarsSum f) x:=by
    let F:= FormalMultilinearSeries.ofScalars A f
    have he : (1:ℝ≥0∞)≤ F.radius := by
      rw [← ENNReal.coe_one]; exact F.le_radius_of_bound 1 (fun i=> by simpa only [F,NNReal.coe_one,one_pow,mul_one,ofScalars_norm] using h i)
    refine F.analyticOnNhd x (lt_of_lt_of_le (b:=(1:ℝ≥0∞)) ?_ he)
    rw [edist_dist, dist_zero_right,← ENNReal.ofReal_one]; exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.2 hx
lemma basicL {x:A}(hx:‖x‖<1): AnalyticAt ℝ log x:= basic priced hx
lemma basicR {x:A}(hx:‖x‖<1): AnalyticAt ℝ rev x:= basic (by simp) hx
omit [CompleteSpace A] in
lemma afford {x:A} (hx:‖x‖<1): Summable (fun n:ℕ=>‖c n • x^n‖):=by
    refine (summable_geometric_of_lt_one (norm_nonneg x) hx).of_nonneg_of_le (fun i=> norm_nonneg _) (fun n=>?_)
    rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (priced _)).trans (norm_pow_le x n)
omit [NormedAlgebra ℝ A] [CompleteSpace A] in
lemma alive {x:A} (hx:‖x‖<1): Summable (fun n:ℕ=> ‖(-x)^n‖):=by
    apply (summable_geometric_of_lt_one (norm_nonneg x) hx).of_nonneg_of_le (fun i=> norm_nonneg _) ; intro n; exact (norm_pow_le _ n).trans_eq (congr_arg (· ^ n) (norm_neg x))
lemma inverse {x:A}(hx:‖x‖<1): (1+x)*rev x=1:=by
    have he:= ((alive hx).of_norm).one_sub_mul_tsum_pow; rw [sub_neg_eq_add,← rev_eq] at he; exact he
-- elementary ODE on a real parameter
private def grad (x:A)(n:ℕ):ℝ→ A
 | t=> match n with | 0=>0|n+1=>(- (t • x))^n *x
omit [NormOneClass A] [CompleteSpace A] in
private lemma differentiate_piece (x:A)(n:ℕ) (t:ℝ):HasDerivAt (fun t:ℝ=> c n • (t • x)^n) (grad x n t) t:=by
    have ht₁:HasDerivAt (fun t:ℝ=>t • x) x t:=by simpa using (hasDerivAt_id' t).smul_const x
    cases n
    · convert! (hasDerivAt_const t (c 0 • (1:A))) using 1; simp only [pow_zero]
    next n=>
      convert! (ht₁.pow (n+1)).const_smul (c (n+1)) using 1
      · simp only [grad,Nat.cast_add_one,Nat.add_sub_cancel]; let y:= (t • x)^n
        rw [show (n:A)+1= (↑(n+1:ℕ) : ℝ) • (1:A) from ?_,smul_mul_assoc, one_mul, smul_mul_assoc,smul_smul,c_succ,Nat.cast_add_one, div_mul_cancel₀ _ (by positivity : (n:ℝ)+1≠0)]
        rw [← smul_mul_assoc,← smul_pow,neg_one_smul]
        push_cast; simp [add_smul,Nat.cast_smul_eq_nsmul,nsmul_eq_mul]
variable [NormedAlgebra ℚ A]
lemma cancel {x:A} (hx:‖x‖ ≤ 1/4): exp (log x)=1+x:=by
    let I:= ball (0:ℝ) 2; let p (t:ℝ):= 1+t • x; let q (t:ℝ):=exp (-log (t • x)); let F(t:ℝ):= q t * p t
    have h0 (y:ℝ)(hy:y∈I):‖y • x‖ ≤ 1/2:=by
       have ht: ‖y‖ ≤ 2:=(dist_zero_right y).symm.trans_le (mem_ball.mp hy).le; rw [norm_smul]; nlinarith only [hx,mul_le_mul ht hx (norm_nonneg _) (by norm_num : (0:ℝ) ≤2)]
    have hx0: (0:ℝ) ∈ I:= mem_ball_self (by norm_num : (0:ℝ) < 2)
    let g0(n:ℕ):ℝ:= match n with|0=>0|n+1=>(1/2:ℝ)^n*‖x‖
    have hgp : Summable g0:= (summable_nat_add_iff 1).mp ((summable_geometric_two).mul_right _)
    have hop : IsOpen I:=isOpen_ball
    have hp : IsPreconnected I:=(convex_ball (0:ℝ) _).isPreconnected
    have hh (t:ℝ)(h:t∈I): HasDerivAt F 0 t:=by
      have h':= (h0 t h).trans_lt (by norm_num : (1/2:ℝ)<1)
      have he : HasDerivAt (fun t:ℝ=>∑' n:ℕ,c n • (t • x)^n) (∑' n,grad x n t) t:=
        hasDerivAt_tsum_of_isPreconnected hgp hop hp (fun n y _=>differentiate_piece x n y) (fun n y hi=> ?grad) hx0 ((afford ((h0 _ hx0).trans_lt (by norm_num : (1/2:ℝ)<1))).of_norm) h
      case grad=> cases n; exact le_of_eq norm_zero; next n=> refine (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) ((norm_neg _).trans_le (h0 _ hi)) _)) (norm_nonneg _))
      simp_rw [← log_eq] at he
      let z:= rev (t • x)
      have hg: (1+t • x)* z=1:= inverse h'
      have hz : ∑' n,grad x n t=z*x:=by
        have ht:= ((alive h').of_norm.hasSum.mul_right x); change HasSum (fun n=> grad x (n+1) t) _ at ht; rw [← rev_eq] at ht
        refine HasSum.tsum_eq ?_
        apply (hasSum_nat_add_iff' 1).mp
        simpa only [Finset.sum_range_one,grad,sub_zero] using ht
      rw [hz] at he
      have hQ : HasDerivAt q (q t * -(z*x)) t:=by
          exact (hasFDerivAt_exp (𝕂:=ℝ)).comp_hasDerivAt t he.neg
      have hP :HasDerivAt p x t:=by
          simpa only [one_smul] using ((hasDerivAt_id' t).smul_const x).const_add (1:A)
      convert! hQ.mul hP using 1
      calc
        (0:A)= q t*(x-1*x) := by simp
        _ = _ := by rw [←hg]; unfold p; ring
    have h := hop.is_const_of_deriv_eq_zero hp (fun x hx=>(hh x hx).differentiableAt.differentiableWithinAt) (fun x hx=>(hh x hx).deriv) (x:=1) (by change _ < (2:ℝ); norm_num) hx0
    have he : exp (-log x)*(1+x)=1:=by simpa [F,p,q] using h
    calc
      _= exp (log x)*(exp (-log x)*(1+x)):=by rw [he,mul_one]
      _=_:=by rw [← mul_assoc,← exp_add_of_commute (Commute.all ..),add_neg_cancel,exp_zero,one_mul]
end YM.Massive.Log
#print axioms YM.Massive.Log.cancel
