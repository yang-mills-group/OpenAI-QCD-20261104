import YM.Elix.Sort
import YM.Analysis.SmoothJets
/-!
  Directional derivatives for Free trace with TRUE slash(0−x) inserted.
  L2 norm not relied. finite.B
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveMasses.FreePair
open Lattice QCD QCD.Lat Maxwell Analysis
open scoped BigOperators Kronecker Matrix.Norms.Frobenius Topology InnerProductSpace
-- spherical factor calculation
noncomputable def rise :E4→ₗ[ℝ]Bundle:= {
   toFun:=fun x=> QCD.Free.slash (fun i=> x i)
   map_add':=fun x y=>by simp only [QCD.Free.slash,PiLp.add_apply, Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
   map_smul':=fun c x=>by simp only [QCD.Free.slash, PiLp.smul_apply,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [smul_eq_mul,Complex.ofReal_mul,mul_smul]; rfl
}
local notation "E"=> basis 2
variable (i j:Axis)(x:E4)
local notation "𝓝p"=> (2*Maxwell.normal)
noncomputable abbrev tube(i:Axis):= wave (gamma i)
noncomputable def fSing (i:Axis):ℝ:= - (4:ℝ)* 𝓝p *(basis i (2:Axis))
local notation "𝕀"=> (0:Axis)
lemma unitN : factor E=𝓝p:=by unfold factor; rw[basis_norm]; ring_nf
lemma dPhi (i:Axis) : ∃ W:E4→L[ℝ] ℝ, HasFDerivAt factor W E∧ W (basis i)=fSing i:=by
     let b:E4→ℝ:=fun x=> ‖x‖^2; obtain ⟨u,h,h₁⟩: ∃ u:E4→L[ℝ] ℝ, HasFDerivAt b u E ∧ u (basis i)= 2*(basis i (2:Axis)):=⟨_,(hasFDerivAt_id (𝕜:=ℝ) (x:=E)).norm_sq,by simp [b,two_mul]⟩ -- has syntax
     obtain ⟨v,hv,h₂⟩:∃ v:E4→L[ℝ]ℝ, HasFDerivAt (fun x=> (b x)⁻¹) v E∧v (basis i) = - u (basis i):= by
           have he:b E=1:=by simp [b]
           refine ⟨_,(hasDerivAt_inv (show b E≠0 from he.symm ▸ one_ne_zero)).hasFDerivAt.comp E h,?_⟩; rw[ContinuousLinearMap.comp_apply]; simp [he] -- derivative sign
     let f(x:E4):= (b x)⁻¹; have he:f E=1:=by simp [f,b]
     have hX:= (hv.mul hv).const_mul (𝓝p:ℝ); refine ⟨(2*normal) • (f E • v+ f E • v), ?_, ?_⟩; -- maybe implicit
     · rw [show factor = _ from (show factor=(fun x=>𝓝p*(f x*f x)) from funext fun x=> by unfold factor; rw [pow_two])]; exact hX
     -- need meta supply F first
     change 𝓝p * (f E * v (basis i)+ f E*v (basis i))=_; rw [he,h₂,h₁]; unfold fSing; ring
noncomputable def cProp (i:Axis): Bundle:= (↑(𝓝p):ℂ) • tube i + (fSing i:ℂ) • tube 2
lemma fertile(a:Axis): rise (basis a)= tube a:=by change (∑ i:Axis, (basis a i:ℂ) • tube i)=_; simp_rw[basis_eq]; simp
lemma dSpin: ∃ W:E4→L[ℝ] Bundle, HasFDerivAt prop W E∧ W (basis i)=cProp i:=by
     obtain ⟨V,hv,h⟩:= dPhi i; let v:= (Complex.ofRealCLM : ℝ→L[ℝ]ℂ); let L:= rise.toContinuousLinearMap
     refine ⟨_, (v.hasFDerivAt.comp E hv).smul (L.hasFDerivAt),?_⟩; change (↑(factor E):ℂ) • rise (basis i)+(↑(V (basis i)):ℂ) • rise E= _; rw [fertile,h,unitN,fertile]; rfl
lemma peaked : prop E=(↑(𝓝p):ℂ) • tube 2:=by unfold prop; rw [unitN]; apply congr_arg; exact fertile _
lemma arch (v w:Bundle) : joined v w (-x)= Matrix.trace (v * prop x*w*prop x):=by rw [joined,neg_neg,prop_neg, mul_neg,neg_mul,neg_mul,Matrix.trace_neg,neg_neg]
lemma pCross(v w:Bundle): D (basis i) (fun y=>joined v w (-y)) E= Matrix.trace (v*cProp i*w*prop E+v*prop E*w*cProp i):=by
     obtain ⟨f,hf,h⟩:=dSpin i; let T:= (Matrix.traceLinearMap Fiber ℝ ℂ).toContinuousLinearMap; rw [show (fun y=>_)=_ from funext fun x=> arch x v w]; unfold D
     let F(x):= v*prop x*w*prop x; let J(x):= v* prop x*w; have hz:= HasFDerivAt.mul' (hf.const_mul v) (hasFDerivAt_const w E); have he:= T.hasFDerivAt.comp E (hz.mul' hf); change fderiv ℝ (T ∘ F) E _=_; change HasFDerivAt (T ∘ F) _ E at he; rw [he.fderiv]; change Matrix.trace (_:Bundle)=_; congr 1
     change J E * f (basis i) + (v * prop E*0+(v * f (basis i))*w)* prop E= _; rw [mul_zero,zero_add,h, add_comm]
end YM.MassiveMasses.FreePair
#print axioms YM.MassiveMasses.FreePair.pCross
