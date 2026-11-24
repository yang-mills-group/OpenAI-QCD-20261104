import YM.QCD.Pearl.Haze

/-! # transverse and longitudinal continuum bubbles. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para Pinch
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology Kronecker
variable {z p k: Momentum}(C:su.Color) (μ:Axis)
lemma trace_gamma (i j: Axis): (gamma i*gamma j).trace=if i=j then (4:ℂ) else 0:=by
  split_ifs with h; · rw [h,gamma_sq,Matrix.trace_one]; simp [Pinor]
  apply neg_eq_self.mp; rw [← Matrix.trace_neg,clifford h, neg_neg, Matrix.trace_mul_comm]; simp [clifford h] -- check
lemma gamma_l (i : Axis): gamma μ*gamma i* gamma μ=if i=μ then gamma i else -(gamma i):=by
  split_ifs with h; · rw [h, gamma_sq,one_mul]
  rw [clifford (Ne.symm h), neg_mul,mul_assoc,gamma_sq,mul_one] -- sign

def lumen (p:Momentum): Spike:=∑ i,p i • gamma i
lemma lite (p) : hiss p=wave (lumen p):=by
  let L:Spike→ₗ[ℂ] Bundle:={ toFun:=wave,map_add':=fun _ _=> (wave_add ..).symm,map_smul':=fun i v=>Matrix.smul_kronecker .. }
  change _=L _; unfold lumen; rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_smul]; rfl
lemma axil (p k: Momentum): (lumen p*gamma μ*lumen k*gamma μ).trace=4*(2*p μ*k μ-∑ i,p i * k i):=by
  have he i :gamma μ*(k i • gamma i)*gamma μ=if i=μ then k i • gamma i else -(k i • gamma i):= by rw [Matrix.mul_smul,Matrix.smul_mul,gamma_l]; split_ifs <;> simp
  have hp : gamma μ*lumen k*gamma μ=(2:ℂ) • (k μ • gamma μ) - lumen k:=by
    unfold lumen; rw [mul_sum,sum_mul]
    have hh i:gamma μ*(k i • gamma i)*gamma μ=(if i=μ then (2:ℂ) • (k μ • gamma μ) else 0)- k i • gamma i:=by
      rw [he]; split_ifs with h; · rw [h,two_smul, add_sub_cancel_right]
      rw [zero_sub]
    simp_rw [hh,sum_sub_distrib, sum_ite_eq',mem_univ,if_true]
  have ht a i:(lumen p*(a • gamma i)).trace= (a:ℂ)*p i*4:=by
    unfold lumen; rw [sum_mul,Matrix.trace_sum]; simp_rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul, trace_gamma,smul_eq_mul,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]; ring
  rw [mul_assoc (lumen p * gamma μ),mul_assoc (lumen p),← mul_assoc (gamma μ),hp,mul_sub,Matrix.mul_smul,Matrix.trace_sub, Matrix.trace_smul, ht];
  rw [show (lumen p * lumen k).trace=∑ i,k i*p i*4 from (by rw [show (lumen p*lumen k)=(∑ i,lumen p*(k i • gamma i)) from Finset.mul_sum ..,Matrix.trace_sum]; simp_rw [ht])]; simp_rw [mul_comm (k _) (p _), ← sum_mul, smul_eq_mul]; ring

def sky (p:Momentum):ℂ:=∑ i,p i^2
lemma cape (k:Momentum):vase shaft k = ((sky k)⁻¹ * (-Complex.I)) • wave (lumen k):=by
  rw [vase,reciprocalP,model_smul]; rw [show quad (shaft k)=sky k by simp [shaft,quad,sky]]
  -- easier
  rw [model]
  simp only [shaft,turn,hiss,Pi.neg_apply,zero_smul,zero_add,neg_smul,sum_neg_distrib,smul_neg]
  rw [← lite]; simp only [hiss,← neg_smul,smul_smul,mul_neg]

lemma glimmer (p k : Momentum)(h : ‖C‖=1): crown (touch (echo C)*wave (gamma μ)) p k=
    3*4 * (2*k μ*(k+p) μ-(∑ i,k i*(k+p : Momentum) i))/(sky k * sky (k+p)):=by
  have he : (echo C*echo C).trace=-3:=by
    have hh:= su.trace_color C C; rw [real_inner_self_eq_norm_sq,h] at hh
    apply Complex.ext; · change ((su.colorMat C *su.colorMat C).trace).re=_; change - ((su.colorMat C *su.colorMat C).trace).re=(3:ℝ)*1^2 at hh; norm_num at *; linarith
    change ((su.colorMat C*su.colorMat C).trace).im= _; rw [su.trace_color_real]; simp
  unfold crown; rw [cape,cape];
  let W:= echo C; let G:=gamma μ; let M:=lumen k; let N:=lumen (k+p); let X:=touch W; let Y:=wave G
  have hm : (wave M*(X*Y)*wave N*(X*Y)).trace=(M*G*N*G).trace*(-3):=by
    unfold X Y wave touch; simp_rw [← Matrix.mul_kronecker_mul,one_mul,mul_one,Matrix.trace_kronecker]; rw [he]
  simp only [Matrix.smul_mul,Matrix.mul_smul, Matrix.trace_smul,smul_eq_mul]
  rw [hm,axil]; simp only [div_eq_mul_inv, mul_inv_rev,← mul_assoc, mul_comm ((sky k)⁻¹)]; ring_nf <;> try (rw [sq Complex.I,Complex.I_mul_I]; ring)
end YM.QCD.Pearl
