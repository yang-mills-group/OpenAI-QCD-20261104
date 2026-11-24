import YM.Heron.Hilt
import YM.Next.MAXWELL.Affine
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Maxwell.Free
open Maxwell (grad)
variable (s:Ortho.Skew)(A:TinG)(Γ:ℝ→EuPin)(hΓ:EuPin.Path s Γ)(i j k:Axis)
local notation "K"=> Ortho.Skew
local notation "C"=> Massive.chargeMatrix
local notation "S"=> -(walt gamma s)
local notation "D"=> sheet s Γ
local notation "L"=> cΩ Γ
set_option quotPrecheck false
local notation "μ" i:arg j:arg => (s.val i j : ℂ)
lemma velvet : S*C+C*(S).transpose=0:=by
    have he(i j:Axis): C*(gamma i*gamma j).transpose= gamma j*gamma i*C:=by
         have ht(i): C*(gamma i).transpose= -(gamma i * C):=by rw [Clifford.transC,neg_neg]
         rw [Matrix.transpose_mul, ←Matrix.mul_assoc,ht,neg_mul,Matrix.mul_assoc _ C,ht,mul_neg,neg_neg,Matrix.mul_assoc]
    unfold walt; simp only[neg_mul, Matrix.transpose_neg,mul_neg, Matrix.transpose_smul, Matrix.transpose_sum,Matrix.smul_mul,Matrix.mul_smul,Finset.mul_sum,Finset.sum_mul,he]; rw [← neg_add,neg_eq_zero,← smul_add];
    have hp : (∑ i:Axis,∑ j:Axis, (μ j i) • (gamma j*gamma i*C))= -(∑ i:Axis,∑ j:Axis,(μ j i) • (gamma i*gamma j*C)):=by
         nth_rw 1[Finset.sum_comm]; rw[← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw[← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; nth_rw 1[skewL s i j]; rw [neg_smul]
    rw [hp,add_neg_cancel,smul_zero]
include hΓ
noncomputable def transP :Spike →L[ℝ] Spike:= LinearMap.toContinuousLinearMap { toFun:=Matrix.transpose,map_smul':=fun x y=>Matrix.transpose_smul ..,map_add':=fun x y=>Matrix.transpose_add ..}
lemma creamy :D*C+C*(D).transpose=0:=by
    let F:= L; have hh : HasDerivAt (fun t => (F t).transpose) ((D).transpose) 0 := transP.hasFDerivAt.comp_hasDerivAt (0:ℝ) (horn s Γ hΓ) -- explicit
    have ht : ∀ t:ℝ,F t*C*(F t).transpose=C:=fun t=> ((euPin_iff _).mp (Γ t).property).1
    have hz: (D*C)*(F 0).transpose+ F 0*C*(D).transpose=0 := by
          apply (((horn s Γ hΓ).mul_const C).mul hh).unique; refine (hasDerivAt_const (x:=0) C).congr_of_eventuallyEq ?_; exact Eventually.of_forall ht -- argument val
    rw [show F 0=1 from cChair s Γ hΓ,Matrix.transpose_one,mul_one,one_mul] at hz; exact hz
lemma might :D=S:=by
   let M:=D-S; have ht(a:Axis):Commute M (gamma a):=by
        change (D-S)*gamma a = gamma a * (D-S); have hp:= fleet s gamma learn a -- arg order
        have hg:= shineL s Γ hΓ a; have h:=hp.trans hg.symm; rw[sub_mul,mul_sub]; rw [show D*gamma a= (S*gamma a-gamma a*S)+gamma a*D from (by rw [h]; abel)]; abel
   let z:= M (0,0) (0,0); have he:M=z • (1:Spike):=Revolve.scalar_spin ht
   have hp:M*C+C*M.transpose=0:=by
        unfold M; rw [sub_mul, Matrix.transpose_sub,mul_sub,show D*C-S*C+(C*(D).transpose-C*(S).transpose)= (D*C+C*(D).transpose)-(S*C+C*(S).transpose) from (by abel),velvet,creamy s Γ hΓ,sub_zero] -- S.transpose
   have hh:C≠0:=by intro hz; have he:=Clifford.charge_sq; rw [show Clifford.C=0 from hz,mul_zero] at he; exact (neg_ne_zero.mpr one_ne_zero) he.symm
   rw [he,Matrix.smul_mul,Matrix.transpose_smul,Matrix.transpose_one,Matrix.mul_smul,one_mul,mul_one,← add_smul] at hp
   have hZ:z=0:=by have ht := (smul_eq_zero.mp hp).resolve_right hh; linear_combination ht/2
   refine sub_eq_zero.mp ((show M=_ from he).trans ?_); rw[hZ,zero_smul]
noncomputable def splice(t:Bool)(p:EuPin): Spike:= if t then (p.matrix.val).transpose else p.matrix⁻¹.val
lemma stems (t:Bool)(x:EuPin)(h:x=1) : splice t x=1:=by subst x; cases t; rfl; exact Matrix.transpose_one
lemma jenna(t:Bool) : HasDerivAt (fun x:ℝ=> splice t (Γ x)) (walt (formT t) s) 0:=by
    have ht := horn s Γ hΓ; rw[might s Γ hΓ] at ht
    cases t
    · have he(x:ℝ): (Γ x)⁻¹ = Γ (-x):=inv_eq_of_mul_eq_one_right (by rw [← MassiveTwoEstimates.SpinParity.additive hΓ, add_neg_cancel,hΓ.1]) -- sign
      have hh: HasDerivAt (fun t:ℝ=> L (-t)) ((-1:ℝ) • S) 0:= by
           have he: HasDerivAt L S (-(0:ℝ)):=by rw [neg_zero]; exact ht
           exact he.scomp (𝕜:=ℝ) (0:ℝ) (by exact (hasDerivAt_id' (0:ℝ)).neg) -- syntax
      have hz: HasDerivAt (fun t:ℝ=> L (-t)) (walt gamma s) 0 := hh.congr_deriv (by rw [neg_one_smul,neg_neg])
      apply hz.congr_of_eventuallyEq; exact Eventually.of_forall fun t=> (congr_arg (fun x:EuPin=>x.matrix.val) (he t))
    have hh: HasDerivAt (transP ∘ cΩ Γ) ((S).transpose) 0:= transP.hasFDerivAt.comp_hasDerivAt (0:ℝ) ht
    rw [Matrix.transpose_neg,dualH,neg_neg] at hh; exact hh
end YM.Heron
#print axioms YM.Heron.jenna
