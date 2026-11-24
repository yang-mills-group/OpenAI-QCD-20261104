import YM.QCD.Oasis.Key
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Cove Golden NormedSpace
variable {L : Side}{j k :ℕ}{t v p x :ℝ}{N :ℕ} {h : EvenA L N}
private lemma pos {i:ℕ}:0≤(8:ℝ)^i:=by positivity
abbrev bundleP {A:Type}[NormedRing A][NormedAlgebra ℝ A](h:A) (n:ℕ): A:=(n.factorial:ℝ)⁻¹ • h^n
noncomputable def mercyK:= ∑' i,‖bundleP (2:ℝ) (i+2)‖
lemma stoutSeries (i:ℕ):‖bundleP (2:ℝ) i‖ = ((i.factorial:ℝ)⁻¹)*(2:ℝ)^i:=by rw [bundleP,norm_smul,Real.norm_of_nonneg (by positivity), norm_pow,Real.norm_of_nonneg (by norm_num)]
lemma mercy (he:‖h‖ ≤ 2*t)(hx:0 < t)(ht:t≤1) : ‖exp h-1-h‖ ≤ t^2 * mercyK := by
   have hi :Summable (fun i=> ‖bundleP h i‖):= norm_expSeries_summable' h
   have hh : exp h - 1-h = ∑' i:ℕ,bundleP h (i+2) := by
       have hp:= (hi.of_norm.sum_add_tsum_nat_add 2);
       rw [exp_eq_tsum ℝ]; unfold bundleP at *; dsimp only; rw [← hp]; rw [Finset.sum_range_succ, Finset.sum_range_succ,Finset.sum_range_zero]; norm_num; abel -- hp
   rw [hh]; have hz := (summable_nat_add_iff 2).2 hi; have hb := norm_expSeries_summable' (𝕂:=ℝ) (2:ℝ)
   have hl i: ‖bundleP h (i+2)‖≤ t^2*‖bundleP (2:ℝ) (i+2)‖:=by
        rw [stoutSeries,bundleP,norm_smul,Real.norm_of_nonneg (by positivity)]; refine (mul_le_mul_of_nonneg_left (norm_pow_le' h (show 0 < i+2 from by omega)) (by positivity : 0 ≤ ((i+2).factorial:ℝ)⁻¹)).trans ?_
        have hv : ‖h‖^(i+2) ≤ 2^(i+2)*t^2:=by apply (pow_le_pow_left₀ (norm_nonneg _) he _).trans; rw [mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx.le ht (by omega)) (by positivity)
        exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (by ring)
   exact (norm_tsum_le_tsum_norm hz).trans ((hz.tsum_le_tsum hl (((summable_nat_add_iff 2).2 hb).mul_left _)).trans_eq (by rw [tsum_mul_left]; rfl))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{φ:E → EvenA L N}{y:E}
def runK (k:ℕ):= clump k 1 (letterP 1 k * mercyK)
set_option maxHeartbeats 470000 in
lemma unpays (h: Brush k t 1 φ y)(hp:0<t)(ht:t≤1): Brush k (t^2 *runK k) 1 (fun i=> exp (φ i)-1-φ i) y:=by
   let g i:= t⁻¹ • φ i
   let A:=(EvenA L N)
   let f (i:EvenA L N):=exp (t • i)-1-t • i
   have he i:t • g i= φ i:= smul_inv_smul₀ hp.ne' _
   have hv':= h.smul t⁻¹; rw [Real.norm_of_nonneg (inv_pos.mpr hp).le,inv_mul_cancel₀ hp.ne'] at hv'
   have hv : Brush k 1 1 g y := hv'
   have hf:AnalyticOnNhd ℂ f Set.univ:=fun i _=>by
     let Q : A→L[ℂ]A:=(t:ℂ) • ContinuousLinearMap.id ℂ A; have hu: AnalyticAt ℂ (fun j:EvenA L N=>t • j) i := Q.analyticAt i
     exact (((NormedSpace.exp_analytic (𝕂:=ℂ) (𝔸:=EvenA L N) _).comp hu).sub analyticAt_const).sub hu
   have hs: Brush k (letterP 1 k *(t^2*mercyK)) 1 f (g y):=by
      apply beau zero_lt_one (fun i _=> (hf i (Set.mem_univ _)).differentiableAt); intro i hi; apply mercy _ hp ht; rw [norm_smul,Real.norm_of_nonneg hp.le,mul_comm (2:ℝ)]; apply mul_le_mul_of_nonneg_left _ hp.le; linarith only [norm_le_norm_add_norm_sub' i (g y),hv.bound, mem_ball_iff_norm.mp hi]
   apply ((composite hv hs).climb ?_ le_rfl).shimmy; · exact Eventually.of_forall fun i=> by change exp _-1-_=f (g i); unfold f; rw [he]
   unfold clump runK clump; apply le_of_eq; ring
end YM.QCD.Oasis
