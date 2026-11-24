import YM.TorusPCAC.Spec.Spin
import YM.QCD.Revolve.Pin

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The matrix gamma-lift computed in exactly the target spin convention

Euclidean side. Coordinate orientation matters even for determinant tests using
reflection, rotations etc. We don't assume exponential conjugation here (check
it explicitly using the infinitesimal formula). **Pin**, not the YM-action.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Spin
open QCD QCD.Lat Lattice Finset NormedSpace Revolve
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius Kronecker

local instance : NormedAlgebra ℚ Spike := .restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _

def direction (T : M4) (i : Axis) := ∑ j, T j i • gamma j
lemma direction_mul (A B : M4) (i : Axis) : direction (A*B) i=∑ j, B j i • direction A j :=by
  unfold direction; simp_rw [Matrix.mul_apply, sum_smul, smul_sum,mul_smul]; rw [sum_comm]; refine sum_congr rfl (fun i _=> sum_congr rfl fun j _=> ?_); rw [smul_comm]
@[simp] lemma direction_one (i : Axis) : direction 1 i=gamma i :=by simp [direction,Matrix.one_apply,ite_smul]

lemma bivector_skew (i j : Axis) : star (bivector i j)=-(bivector i j) :=by
  unfold bivector; split; next=> simp
  next h=> rw [star_smul,star_mul, gamma_star,gamma_star,clifford (Ne.symm h),smul_neg]; norm_num

lemma circular_exp (i j k : Axis) : bivector i j * gamma k - gamma k * bivector i j=direction (Ortho.plane i j).val k:=by
  unfold bivector direction Ortho.plane; by_cases h:i=j
  · subst j; simp
  rw [if_neg h]; set I:=gamma i; set J:=gamma j
  have he : I*I=1:= gamma_sq i; have hh:J*J=1:= gamma_sq j
  have hp:I*J=-(J*I):=clifford h; have ht:J*I=-(I*J):=clifford (Ne.symm h)
  by_cases h₁:i=k
  · subst k
    rw [Matrix.smul_mul,Matrix.mul_smul,← smul_sub]; rw [show I*J*I-I*(I*J)= (2:ℂ) • (-gamma j) from (by rw [hp, neg_mul,mul_assoc J I,he,mul_one,← hp,← mul_assoc I I,he,one_mul]; rw [two_smul]; change _ = -J + -J; abel), smul_smul,inv_mul_cancel₀ (by norm_num),one_smul]
    simp [Matrix.single, ite_smul,Ne.symm h]
  by_cases h₂:j=k
  · subst k
    rw [Matrix.smul_mul,Matrix.mul_smul,← smul_sub]; rw [show I*J*J-J*(I*J)= (2:ℂ) • gamma i from (by rw [mul_assoc I J, hh,mul_one,← mul_assoc J I,ht, neg_mul,mul_assoc, hh,mul_one, two_smul]; change _=I+I; abel), smul_smul,inv_mul_cancel₀ (by norm_num),one_smul]
    simp [Matrix.single,ite_smul,h]
  rw [Matrix.smul_mul,Matrix.mul_smul]; rw [mul_assoc, show J*gamma k=-(gamma k*J) from clifford h₂,mul_neg,← mul_assoc, show I* gamma k= _ from clifford h₁,neg_mul,mul_assoc,neg_neg]; simp [Matrix.single,h₁,h₂,I]

lemma evolves (x : Spike): (evolve x).val=exp x:=by unfold evolve; rw [IsUnit.unit_spec]; rfl
lemma journey (i j k : Axis) (t : ℝ) : let b:=rotations i j t; b.2.val*gamma k=direction b.1.val k*b.2.val :=by
  let H := (Ortho.plane i j).val; let B:=bivector i j; let R (t:ℝ):=exp (t • H); let S (t:ℝ):=exp (t • B); let V(t:ℝ):=exp (t • (-B))
  let L := LinearMap.toContinuousLinearMap (show M4→ₗ[ℝ] Spike from { toFun:= fun A=>direction A k, map_add':=fun A B=>by simp [direction,add_smul,sum_add_distrib], map_smul':=fun a x=>by simp [direction,mul_smul,smul_sum] });
  have he (u:ℝ) : L (H*R u)=B*L (R u) - L (R u)*B:=by
    change direction _ _= B*(∑ j, R u j k • gamma j)-(∑ j, R u j k • gamma j)*B; rw [direction_mul, mul_sum,sum_mul,← sum_sub_distrib]; refine sum_congr rfl fun b _=>?_ ; rw [smul_mul_assoc,mul_smul_comm,← smul_sub, circular_exp]
  have hh (u:ℝ) : HasDerivAt (fun a=> V a * L (R a) * S a) 0 u:=by
    have hv : HasDerivAt (fun t : ℝ=>V t * L (R t)* S t) ((V u*(-B)*L (R u)+V u*L (H*R u))*S u + V u*L (R u)*(B*S u)) u := ((hasDerivAt_exp_smul_const (-B) u).mul (L.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_exp_smul_const' H u))).mul (hasDerivAt_exp_smul_const' B u)
    rw [he, show V u*(-B)*L (R u)= V u * (-B)*L (R u) from rfl] at hv -- redundant
    convert hv using 1; noncomm_ring
  have hp:V t * L (R t)* S t=gamma k:=by
    have hv : V t * L (R t)* S t= V 0 * L (R 0)* S 0:=is_const_of_deriv_eq_zero (fun x=> (hh x).differentiableAt) (fun x=>(hh x).deriv) t 0
    rw [hv]; simp [S,V,L,R]
  have ht:S t * V t=1:=by rw [show V t=exp (-(t • B)) by unfold V; rw [smul_neg], show S t=exp _ from rfl]; exact (exp_add_of_commute (Commute.refl (t • B)).neg_right).symm.trans (by rw [add_neg_cancel]; exact exp_zero)
  simp only [rotations, Ortho.oneParameter,evolves]; change S t * gamma k=L (R t)*S t; rw [← hp,← mul_assoc,←mul_assoc,ht,one_mul]
end YM.TorusPCAC.Spin

#print axioms YM.TorusPCAC.Spin.journey
