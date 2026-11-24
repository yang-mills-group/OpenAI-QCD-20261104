import YM.Heron.Thaw
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (fromCenter)
open Maxwell (grad)
open Finset MvPolynomial
variable {d:ℕ}(s:Ortho.Skew)(Γ:ℝ→EuPin)(h:EuPin.Path s Γ)(x:ℝ)(p q:Multi d)(i j:Axis)
local notation "T"=> multiMove
include h
lemma xPoint(p:Multi d)(a:Axis)(H:AtNext a p q): changeP (Γ x) (walk q)= stencilFrame (Γ x) a* ∑ k:Multi d,T (Γ x) p k • walk k:=by rw[sprouted p q a H,map_mul,collect (x:=p),changeP,aeval_X]
set_option quotPrecheck false
local notation "P" k:arg=> (MvPolynomial.X k: MvPolynomial Axis ℂ)
lemma opes (r:Multi d)(a:Axis)(H:AtNext a r p): T (Γ x) p q=∑ i:Axis,∑ k:Multi d, (((Γ x).coord.val i a):ℂ)* T (Γ x) r k * coeff (token q) ((P i)*walk k):=by
    rw[modal,xPoint s Γ h x p r a H,stencilFrame, Finset.sum_mul, MvPolynomial.coeff_sum]; apply sum_congr rfl; intro i _; rw [Finset.mul_sum,MvPolynomial.coeff_sum]; apply sum_congr rfl; intro j _; rw [mul_assoc,MvPolynomial.coeff_C_mul, mul_smul_comm (T (Γ x) r j),MvPolynomial.coeff_smul]; simp only[smul_eq_mul,mul_assoc]
lemma modesP(a i:Axis):DifferentiableAt ℝ (fun t:ℝ=> (((Γ t).coord.val i a):ℂ)) 0:= (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (cSpan s Γ h i a)).differentiableAt
lemma hops : DifferentiableAt ℝ (fun x=> multiMove (Γ x) p q) 0:=by
    induction h':UV.order (power p) using Nat.strong_induction_on generalizing p q with
    | h k ih=>
       subst k; by_cases he:p=0
       · subst p; simp_rw [modal,walking]; simp only [show ∀ i:Axis,power (0:Multi d) i=0 from fun _=>rfl,pow_zero, prod_const_one,map_one]; exact differentiableAt_const _
       obtain ⟨a,r,H⟩:= prey p he; have hq:UV.order (power r)<UV.order (power p):=by rw[Arise.omegaLen H]; omega
       simp_rw [fun x=>opes s Γ h x p q r a H]; exact DifferentiableAt.fun_sum fun i _=> DifferentiableAt.fun_sum fun j _=> ((modesP s Γ h _ _).mul (ih _ hq r j rfl)).mul_const _
lemma fibre(t:Bool)(i j:Pinor):DifferentiableAt ℝ (fun x:ℝ=> splice t (Γ x) i j) 0:=by
    let F:Spike→ₗ[ℝ]ℂ:={ toFun:=fun x=> x i j,map_add':=fun x y=>rfl,map_smul':=fun a x=>rfl }; exact F.toContinuousLinearMap.differentiableAt.comp 0 (jenna s Γ h t).differentiableAt
end YM.Heron
#print axioms YM.Heron.fibre
#print axioms YM.Heron.hops
