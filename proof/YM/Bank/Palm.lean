import YM.Bank.Kith
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Palm
open Function Wilson Lattice Laurent Bloch Metric Precision RG Filter Next.Free Pap Bee Pilot Murmur Kith Analysis
open MeasureTheory Finset Maxwell
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff ComplexConjugate NNReal BigOperators InnerProductSpace
variable {e s r t  C R:ℝ}{x:E4}
lemma Ecore (l:List Axis){f:E4→ℂ}(h: ContDiffAt ℝ ∞ f x):ContDiffAt ℝ ∞ (earn l f) x:=by induction l with
   | nil=> exact h
   | cons _ l ih=> exact dSmooth ih _ (by simp)
lemma Ebase (l:List Axis) {f g:E4→ℂ} (h:f=ᶠ[𝓝 x] g):earn l f=ᶠ[𝓝 x] earn l g:=by induction l with
   | nil=> exact h
   | cons _ l ih=> exact ih.eventuallyEq_nhds.mono (fun y hy=> GermD _ hy)
lemma scaler (f:E4→ℂ){g:E4→ℂ} (t r:ℝ) (hr:0<r)(hg:∀ y∈ Maxwell.away,ContDiffAt ℝ ∞ f y)(he: ∀ y∈Maxwell.away,g (r • y)=(t:ℂ) • f y)(hy:∀ y∈Maxwell.away,ContDiffAt ℝ ∞ g y) (l:List Axis)(hx:x≠0): earn l g (r • x)=(t/(r^l.length):ℝ) • earn l f x:=by
    induction l generalizing x with
    | nil=> simpa [earn,Complex.real_smul] using he x hx
    | cons a l ih=>
       let F:=earn l f; let G:=earn l g; let s:=t/r^l.length; let A:=basis a; let L: E4→L[ℝ] E4:= r • ContinuousLinearMap.id ℝ E4
       have hU: L x ≠0:= smul_ne_zero hr.ne' hx
       have hb : (G ∘ L) =ᶠ[𝓝 x] (s • F):= (show ∀ᶠ y in 𝓝 x,y≠0 from Maxwell.open_away.mem_nhds hx).mono fun y h=> ih h -- implicit x explicit?
       have hD:=Ecore l (hy (L x) hU); have hF :=Ecore l (hg x hx)
       have hk : Analysis.D A (G ∘ L) x=Analysis.D A (s • F) x:= GermD _ hb
       unfold Analysis.D at hk
       rw [fderiv_comp _ (hD.differentiableAt (by simp)) L.differentiableAt,L.fderiv, fderiv_const_smul (hF.differentiableAt (by simp))] at hk
       have hz:fderiv ℝ G (L x) (r • A)= s • fderiv ℝ F x A:=hk
       rw [map_smul] at hz
       change fderiv ℝ G (L x) A= _ • fderiv ℝ F x A
       rw [List.length_cons,pow_succ,←div_div]; apply smul_right_injective _ hr.ne'; dsimp only; rw [hz, smul_smul,mul_div_cancel₀ _ hr.ne']
def current (l:List Axis)(x:E4):=earn l (fun y=> (Green y :ℂ)) x
lemma fare (l:List Axis){x:E4}(hx:x≠0)(ht:0<t): current l (t • x)=(t^(2+l.length))⁻¹ • current l x:=by
    unfold current; rw [scaler (fun x=> (Green x:ℂ)) (t⁻¹^2) t ht ?_ ?_ ?_ l hx]; congr 1; rw [pow_add,inv_pow,_root_.mul_inv]; ring
    all_goals intro y hy; change y≠0 at hy
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (freeSmooth hy)
    · rw [Green,Green,norm_smul,Real.norm_of_nonneg ht.le, mul_pow,_root_.mul_inv, inv_pow]; push_cast; simp; ring
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (freeSmooth hy)
lemma dealtS (t:ℝ)(y:E4)(h:y≠0):ContDiffAt ℝ ∞ (fun x=> (hired t x:ℂ)) y:= Complex.ofRealCLM.contDiff.contDiffAt.comp y ((freeSmooth h).mul (show ContDiff ℝ ∞ (fun x:E4=> (1-Real.exp (-‖x‖^2/(4*t)))) from by
   apply contDiff_const.sub; have hi:= (contDiff_norm_sq ℝ (E:=E4) (n:=∞)).neg; rw [show (fun x:E4=>Real.exp (-‖x‖^2/(4*t)))= fun x=> Real.exp (-(‖x‖^2)*(4*t)⁻¹) by ext; ring]; exact (hi.mul contDiff_const).exp).contDiffAt)
def lively (l:List Axis)(t:ℝ):= earn l (fun y=> (hired t y:ℂ))
lemma deed (l:List Axis)(hx:x≠0)(ht:0<t): lively l t (t • x) = (t^(2+l.length))⁻¹ • lively l t⁻¹ x:=by
    unfold lively; rw [scaler (fun y=> (hired t⁻¹ y:ℂ)) (t⁻¹^2) t ht ?_ ?_ ?_ l hx]; congr 1; rw [pow_add,inv_pow,_root_.mul_inv]; ring
    all_goals intro y hy
    · exact dealtS _ _ hy
    · unfold hired; rw [show Green (t • y)=t⁻¹^2*Green y from (by unfold Green; rw [norm_smul, Real.norm_of_nonneg ht.le, mul_pow, _root_.mul_inv, inv_pow]; ring),norm_smul,Real.norm_of_nonneg ht.le, show -(t*‖y‖)^2/(4*t)=-‖y‖^2/(4*t⁻¹) from (by field_simp)]; push_cast; simp[mul_assoc]
    exact dealtS _ _ hy

-- regulate remains being exponentially small even after many position derivatives.
def wink (t:ℝ)(x:E4):ℝ:=Real.exp (t*(-‖x‖^2/4))
lemma winked (t:ℝ):ContDiff ℝ ∞ (wink t):=by unfold wink; simp_rw [div_eq_mul_inv]; exact (contDiff_const.mul ((contDiff_norm_sq ℝ).neg.mul contDiff_const)).exp
lemma wink_f (t:ℝ)(x:E4)(A: Axis): Analysis.D (basis A) (fun y=> (wink t y:ℂ)) x = ((wink t x *t*(-x A/2):ℝ):ℂ):=by
    let U:=basis A
    have hp := ((((hasStrictFDerivAt_norm_sq x).hasFDerivAt.neg.mul_const ((4:ℝ)⁻¹)).const_mul t).exp)
    have hh : wink t=(fun y:E4=> Real.exp (t*(-‖y‖^2*(4:ℝ)⁻¹))) :=by ext; simp [wink,div_eq_mul_inv]
    unfold Analysis.D; rw [hh]; dsimp only; rw [show fderiv ℝ (fun y:E4=> (↑(Real.exp (t*(-‖y‖^2*4⁻¹))) : ℂ)) x=_ from (Complex.ofRealCLM.hasFDerivAt.comp x hp).fderiv] -- syntax
    simp [two_smul,basis_inner,real_inner_comm x];  rw [← real_inner_comm x,basis_inner]; ring
lemma spr (l:List Axis):∃ (n:ℕ) (F: Fin n→ ℕ) (Z: Fin n→ E4→ℂ), (∀ i y,y∈away→ContDiffAt ℝ ∞ (Z i) y) ∧ ∀ t:ℝ,∀ x:E4,x∈away→
     lively l t⁻¹ x-current l x=(wink t x:ℂ)* ∑ i,(t:ℂ)^(F i)*Z i x:=by
   induction l with
   | nil=> refine ⟨1,fun _=>0,fun _ y=> -(Green y:ℂ), (fun i y hy=> (Complex.ofRealCLM.contDiff.contDiffAt.comp y (freeSmooth hy)).neg),fun t x h=>?_⟩
           simp only [lively,earn,current,List.foldr_nil]; unfold wink hired; rw [show -‖x‖^2/(4*t⁻¹)=t*(-‖x‖^2/4) by ring_nf; simp]; push_cast; simp; ring
   | cons a l ih=>
         obtain ⟨n,F,Z,hz,H⟩:=ih; let g(i: Fin n) (y:E4):ℂ:=(-y a/2:ℝ)*Z i y
         let B:= Fin n ⊕ Fin n; let e:B≃ Fin (n+n):=finSumFinEquiv
         let f:B→ℕ:= Sum.elim F (fun i=>F i+1); let U:=basis a; let Y:B→E4→ℂ:=Sum.elim (fun i=>Analysis.D U (Z i)) g
         refine ⟨_,f∘e.symm,Y∘e.symm,?_,fun t x hh=>?_⟩
         · intro i y h; obtain ⟨(i|i),rfl⟩:=e.surjective i <;> simp only [comp_apply, e.symm_apply_apply]
           · exact dSmooth (hz i y h) U (by simp)
           unfold Y g; change ContDiffAt ℝ ∞ (fun x:E4=> ((-x a/2:ℝ):ℂ)*Z i x) y; exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y ((compAxis a).contDiff.contDiffAt.neg.div_const _)).mul (hz i _ h)
         let S (t:ℝ)(x:E4):= ∑ i,(t:ℂ)^(F i)*Z i x; let W(x:E4):= (wink t x:ℂ)
         have hS i : DifferentiableAt ℝ (fun x => (t:ℂ)^(F i)*Z i x) x:= (differentiableAt_const _).mul ((hz i _ hh).differentiableAt (by simp))
         have hP:= Ecore l (dealtS t⁻¹ x hh); have hX := Ecore l (Complex.ofRealCLM.contDiff.contDiffAt.comp x (freeSmooth hh))
         have hT:= Analysis.GermD U (show (lively l t⁻¹-current l) =ᶠ[𝓝 x] fun y=> W y*S t y from Eventually.mono (open_away.mem_nhds hh) (fun y h=> H t y h))
         have hW:= Complex.ofRealCLM.contDiff.contDiffAt.comp x (winked t|>.contDiffAt); change ContDiffAt ℝ ∞ W x at hW
         have hk : fderiv ℝ (S t) x U=∑ i,(t:ℂ)^(F i)*Y (Sum.inl i) x:=by
             unfold S; rw [fderiv_fun_sum (fun i _=>hS i)]; rw [ContinuousLinearMap.sum_apply]; refine sum_congr rfl fun i _=>?_;
             rw [fderiv_const_mul ((hz i _ hh).differentiableAt (by simp)) _]; rfl
         unfold Analysis.D at hT; rw [fderiv_sub (show DifferentiableAt ℝ (lively l t⁻¹) x from hP.differentiableAt (by simp)) (show DifferentiableAt ℝ (current l) x from hX.differentiableAt (by simp)), fderiv_fun_mul (hW.differentiableAt (by simp)) (show DifferentiableAt ℝ (S t) x from DifferentiableAt.fun_sum fun i _=> hS i)] at hT
         change fderiv ℝ (lively l t⁻¹) x U-fderiv ℝ (current l) x U=_
         rw [show _ - _ =_ from hT] -- convert
         rw [← Equiv.sum_comp e _]; simp only [Fintype.sum_sum_type, Finset.mul_sum, ContinuousLinearMap.add_apply,comp_apply,e.symm_apply_apply]
         simp only [ContinuousLinearMap.smul_apply, hk,smul_eq_mul, show fderiv ℝ W x U=_ from wink_f t x a]; unfold S; push_cast; simp only [mul_add, Finset.mul_sum,W]; unfold B; rw [Finset.sum_mul,Fintype.sum_sum_type]; congr 1
         apply sum_congr rfl; intro i _; unfold f Y g; simp; ring
end YM.Bank.Palm
#print axioms YM.Bank.Palm.spr
