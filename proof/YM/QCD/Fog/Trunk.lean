import YM.QCD.Fog.Estate

/-! # score normalization with actual Bed condition. Costs -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid YM.Next.Free Matrix Placement
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable (T:Bed) {r A C d a:ℝ}{n:Side}{I:Type}
lemma voteG (T:Signed → ℝ) (a:ℝ) (h:∀ i, T i=a):Patch.average T=a:=by
  unfold Patch.average; simp only [h,Finset.sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ (show (↑(Fintype.card Signed):ℝ)≠0 by positivity)]
lemma budgetE (hp:T.metric.strip r A)(hr: 0<r) (x:Dir su n): total (plain ∘ boot T) (flux x)=gaugeFiscal T x x/2:=by
  let L:= plain ∘ boot T; let F:=flux x
  have he i : dotProduct (parts su 1 x i) ((K (T.metric.acts n))*ᵥ parts su 1 x i)=∑ y:Site n, ∑ p:PlaqAxes, F p i y * (∑ q:PlaqAxes,∑' z:Cover,rateG T (p,q,z) * F q i (y+wrap n z)):=by
    let M:= d 1 n *ᵥ parts su 1 x i
    unfold Precision.K; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro y _
    rw [← Equiv.sum_comp plaqEquiv]; refine Finset.sum_congr rfl fun p _=> ?_; change F p i y*(T.metric.acts n *ᵥ M) _= _; congr 1
    rw [output_row T.metric M (Bloch.Row.rights _ _ hp hr.le), ← Equiv.sum_comp plaqEquiv]; rfl
  unfold gaugeFiscal; simp_rw [he]; let S:=Site n
  have hv:= bootBill T hp
  rw [total, Summable.tsum_finsetSum (fun i _=> sample_summable (plain ∘ boot T) (flux x) hr.le hv i),sum_comm (s:=univ) (t:=univ) (f:=fun i y=>∑ p:PlaqAxes,_),sum_div] -- binder metavars
  apply sum_congr rfl; intro i _
  have h:= sample_summable (plain ∘ boot T) (flux x) hr.le hv i; rw [h.tsum_prod,tsum_fintype, sum_comm (s:=univ) (t:=univ),sum_div] -- wrong side
  apply sum_congr rfl; intro P _
  rw [(h.prod_factor P).tsum_prod,tsum_fintype]; simp_rw [mul_sum]; rw [sum_comm (s:=univ) (t:=univ),sum_div]
  apply sum_congr rfl; intro Q _
  simp_rw [sum_div, ← tsum_mul_left,← tsum_div_const]; rw [← Summable.tsum_finsetSum (fun j _=>?_)]
  · apply tsum_congr; intro a; rw [Function.comp_apply,plain_flux,boot_poly]; simp only [boot,Matrix.cons_val_zero,Matrix.cons_val_one, Matrix.cons_val_fin_one,slotFace,slot_offset, slot_plaq,map_zero,zero_add,inner_color (G:=su), mul_sum]; apply sum_congr rfl; intro b _; unfold F Iteration.flux; rw [add_comm (wrap _ _)]; ring
  have h := sums_mul_shift (n:=n) (R:=T.metric) (Bloch.Row.rights _ _ hp hr.le) (b:=plaquette Q) (Exterior.d 1 n *ᵥ parts su 1 x j) (plaquette P) i
  exact (h.mul_left (F P j i)).div_const 2
