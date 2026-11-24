import YM.QCD.Raft.Lodge

/-! # op norm of response jets from localized entries -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Cost Push.Uniform Eyrie Stationary Quarry Run Kit YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f n:Side}{r C:ℝ}{F:Cnr n→Sheet n}
-- Schur
lemma scatter {I:Type}[Fintype I][DecidableEq I](A:Mx I)(hr:0≤C)(hx:∀ i,∑ j, ‖A i j‖≤C)(hy:∀ i,∑ j, ‖A j i‖≤C): ‖A‖≤ C:=by
  rw [lead_norm]; refine ContinuousLinearMap.opNorm_le_bound _ hr (fun x=>?_)
  let B (i:I):=‖(lead A x) i‖
  have ht (i): B i ^ 2≤ C*∑ j, ‖A i j‖ *‖x j‖^2:=by
    have hh : B i ≤ ∑ j, ‖A i j‖ * ‖x j‖:=by simp_rw [← norm_mul]; exact norm_sum_le ..
    apply (pow_le_pow_left₀ (show 0≤ B i from norm_nonneg _) hh 2).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (hx i) (sum_nonneg fun j _=> by positivity))
    let f j:=Real.sqrt ‖A i j‖; let g j:= f j*‖x j‖; have hu j:f j^2= ‖A i j‖:=Real.sq_sqrt (by positivity)
    have hF:= Finset.sum_mul_sq_le_sq_mul_sq univ f g
    have he j:f j*g j= ‖A i j‖*‖x j‖:=by unfold g; rw [← mul_assoc,← sq,hu]
    simp_rw [he,g,mul_pow,hu] at hF; exact hF
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg x)),EuclideanSpace.norm_sq_eq,mul_pow,EuclideanSpace.norm_sq_eq]
  apply (sum_le_sum (s:=univ) (fun i _=> ht i)).trans; rw [← Finset.mul_sum,Finset.sum_comm, sq,mul_assoc]; apply mul_le_mul_of_nonneg_left _ hr; rw [Finset.mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)

def pricesG (r:ℝ):= (Fintype.card Fiber :ℝ)*countCost r
def level (n:ℕ)(r D:ℝ):= D* ((Fintype.card (Exterior.TypeFace 1 × su.ColorIndex):ℝ)*countCost r)^n
lemma pricepos (ht:0<r):0≤ pricesG r:=mul_nonneg (by positivity) (count_pos ht).le
lemma level_nn (hc:0≤C)(ht:0<r)(n:ℕ):0≤ level n r C:=mul_nonneg hc (pow_nonneg (mul_nonneg (by positivity) (count_pos ht).le) _)
lemma tracks {D:Sheet n}(ht:0<r)(hc:0≤C)(he:∀ i j:Row n, ‖D i j‖≤ C*Decay r i.1 j.1): ‖D‖≤ C *pricesG r:=by
  apply scatter D (mul_nonneg hc (pricepos ht)) (fun i=>?_) (fun i=>?_)
  · apply (sum_le_sum (s:=univ) fun j _=> he i j).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (Multiplicity.count _ (multIF n) ht _) hc
  apply (sum_le_sum (s:=univ) fun j _=> he j i).trans; rw [← mul_sum]; simp_rw [decay_comm r _ i.1]; exact mul_le_mul_of_nonneg_left (Multiplicity.count _ (multIF n) ht _) hc
lemma periods (ht:0<r)(hc:0≤C)(h:Eyrie.glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst F r C)(x:Cnr n): ‖blade x F 0‖ ≤ level 1 r C * ‖x‖*pricesG r ∧ ‖Jacobi.mixed x x F 0‖≤ level 2 r C * ‖x‖ * ‖x‖ * pricesG r:=by
  have hp:ContDiffAt ℝ ω F 0:=matrix_g fun i j=>(h i j).host
  constructor
  · apply tracks ht (mul_nonneg (level_nn hc ht _) (norm_nonneg _)); intro i j
    rw [detailed hp]; unfold blade; nth_rw 1 [Sparks.bolt_add x]; rw [map_sum]; apply (norm_sum_le ..).trans
    apply le_trans (sum_le_sum (g:=fun k:Road n=> ‖x‖*(C*Decay r i.1 j.1 * Decay r i.1 k.1)) ?_)
    · simp_rw [mul_assoc _,← Finset.mul_sum]
      let q:= (Fintype.card (Exterior.TypeFace 1 × su.ColorIndex):ℝ)
      have ht : ∑ k:Road n,Decay r i.1 k.1≤ q * countCost r:= Multiplicity.count _ (multIF n) ht _
      unfold level; rw [pow_one]; dsimp only [q] at ht
      linarith only [mul_le_mul_of_nonneg_left ht (mul_nonneg (mul_nonneg (norm_nonneg x) hc) (decay_pos r i.1 j.1).le)]
    intro k _; rw [map_smul, norm_smul]; exact mul_le_mul (norm_le_pi_norm x k) ((h i j).walks k) (norm_nonneg _) (norm_nonneg _)
  let g:Ratio n n:= {count:= 1, exact_size:=by simp}; have he: beam g=traceG n:=by funext i; unfold beam Lattice.Ratio.embed; rw [show g.count.val=1 from rfl,one_smul,wrap_lift]
  exact tracks ht (mul_nonneg (mul_nonneg (level_nn hc ht _) (norm_nonneg _)) (norm_nonneg _)) fun i j=>Smoke.grantP (g:=g) F x x ht hc (by rw [he]; exact h) i j
end YM.QCD.Raft
