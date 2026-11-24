import YM.QCD.Raft.Ocean

/-! # Uniform determinant Hessian bound substrate. price HS; avoids dependence on the maximal inverse singular value of the full D. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Matrix Cost
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {I:Type} [Fintype I] [DecidableEq I]

def hs2 (A:Mx I):ℝ:= ∑ i,∑ j,‖A i j‖^2
lemma hsPos (A:Mx I):0≤hs2 A:=sum_nonneg fun i _=> sum_nonneg fun j _=>sq_nonneg _
lemma Hunit (A :Mx I)(U:Mx I)(h:U∈ unitary _):hs2 (U*A)=hs2 A:=by
  unfold hs2; rw [Finset.sum_comm (f:=fun i j=> ‖(U*A) i j‖^2),Finset.sum_comm (f:=fun i j=> ‖A i j‖^2)]; apply sum_congr rfl; intro i _
  let X:= WithLp.toLp 2 (fun j=> A j i); have ht:= unitary_moves U h X; exact Eq.trans (EuclideanSpace.norm_sq_eq (𝕜:=ℂ) (op U X)).symm ((congr_arg (fun x:ℝ=>x^2) ht).trans (EuclideanSpace.norm_sq_eq ..))
lemma flipH (A:Mx I): hs2 (star A)=hs2 A:=by unfold hs2; rw [sum_comm (f:=fun i j=> ‖(star A) i j‖^2)]; simp [Matrix.star_eq_conjTranspose]
lemma HunitR (A :Mx I)(U:Mx I)(h:U∈unitary _): hs2 (A*U)=hs2 A:=by rw [← flipH (A*U),star_mul,Hunit _ _ (Unitary.star_mem h),flipH]
lemma hleft (A V:Mx I): hs2 (A*V)≤ ‖A‖^2*hs2 V:=by
  unfold hs2; rw [Finset.sum_comm (f:=fun i j=> ‖(A*V) i j‖^2), Finset.sum_comm (f:=fun i j=> ‖V i j‖^2), Finset.mul_sum]; apply sum_le_sum; intro i _
  let X:=WithLp.toLp 2 (fun j=> V j i)
  have he : ‖lead A X‖^2=∑ j, ‖(A*V) j i‖^2:=EuclideanSpace.norm_sq_eq ..
  have hm : ‖X‖^2=∑ j, ‖V j i‖^2:=EuclideanSpace.norm_sq_eq _
  rw [← he, ← hm, ← mul_pow]; gcongr; exact leanBound ..
lemma hright (A V:Mx I):hs2 (A*V) ≤ ‖V‖^2*hs2 A :=by rw [← flipH (A*V),star_mul,← flipH A,← norm_star V]; exact hleft ..
lemma trace_sq (A B:Mx I): ‖Matrix.trace (A*B)‖ ≤ Real.sqrt (hs2 A) *Real.sqrt (hs2 B):=by
  let f (i:I×I):= ‖A i.1 i.2‖; let g (i:I×I):= ‖B i.2 i.1‖
  have ht: (A*B).trace=∑ i:I × I,A i.1 i.2* B i.2 i.1:= by rw [Fintype.sum_prod_type]; rfl
  rw [ht]; apply (norm_sum_le ..).trans; simp_rw [norm_mul]; apply (Real.sum_mul_le_sqrt_mul_sqrt (univ) f g).trans_eq; unfold hs2 f g; rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm (s:=univ) (t:=univ) (f:=fun i j=> ‖B j i‖^2)]
lemma hId : hs2 (1:Mx I)= Fintype.card I:=by simp [hs2,Matrix.one_apply,apply_ite (fun i:ℂ=> ‖i‖),ite_pow]
lemma trace_one (A :Mx I): ‖A.trace‖ ≤ Real.sqrt (hs2 A) * Real.sqrt (Fintype.card I) :=by rw [← hId]; nth_rw 1 [← mul_one A]; exact trace_sq ..
lemma htrace (A V:Mx I): ‖(A*V).trace‖ ≤ (‖V‖ *Real.sqrt (hs2 A))*Real.sqrt (Fintype.card I):=by
  apply (trace_one _).trans; apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _); rw [← Real.sqrt_sq (norm_nonneg V),← Real.sqrt_mul (sq_nonneg _)]; exact Real.sqrt_le_sqrt (hright ..)
lemma htrace_two (A V:Mx I): ‖(A*V*(A*V)).trace‖ ≤ ‖V‖^2*hs2 A :=by
  apply (trace_sq ..).trans; rw [← sq,Real.sq_sqrt (hsPos _)]; exact hright ..
end YM.QCD.Raft
