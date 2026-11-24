import YM.DawnS.Blurb
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct
local notation "Y"=>Vertex
local notation "P"=>RingS
local notation "B"=>basis timeAxis
local notation "Ω"=>muS
local notation "I₀"=>Complex.I
local notation "DΓ"=> Arise.Range.deriveL
variable {r s t:ℝ}(hr:0<r)(hp:|s|=r)(he:s=t*r)
local notation "K"=> (timeAxis:Axis)
lemma roofing {ι:Type}[Fintype ι](Q:ι→ℂ)(f:ι→ E4→ℂ)(hf:∀ i x,x∈away → ContDiffAt ℝ ∞ (f i) x)(l:List Axis)(x:E4)(hx:x∈away): deriveL l (fun y=>∑ i:ι,Q i*f i y) x= ∑ i,Q i * deriveL l (f i) x:=by
     classical
     induction l generalizing f x with
     | nil=> rfl
     | cons a l ih=>
            refine Eq.trans (GermD (basis a) ((show deriveL l _=ᶠ[𝓝 x] (fun y=>∑ i:ι,Q i* deriveL l (f i) y) from (show ∀ᶠ y in 𝓝 x, y∈away from open_away.mem_nhds hx).mono (fun y hy=>ih f hf y hy)))) ?_
            have ht(i:ι): DifferentiableAt ℝ (deriveL l (f i)) x := (balla l _ _ open_away (hf i) x hx).differentiableAt (by simp)
            unfold Analysis.D; rw [fderiv_fun_sum (A:=fun i y=>Q i*deriveL l (f i) y) (fun i _=>(differentiableAt_const (Q i)).mul (ht i)),ContinuousLinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw[fderiv_const_mul (ht i) (Q i)]; rfl
lemma derived_res(a b:Pinor) (l:List Axis)(x:E4)(hx:x≠0):deriveL l (dirac a b) x= -∑ j:Axis, gamma j a b * (↑(deriveL l (grad j Green) x):ℂ):=by
     let f(i:Axis): E4→ℂ := Complex.ofRealCLM ∘ grad i Green
     have h(i:Axis): ∀ x∈away,ContDiffAt ℝ ∞ (grad i Green) x:= fun x hx=> gradGradientSmooth hx _
     rw [show dirac a b=(fun y=> ∑ j:Axis, -(gamma j a b)* f j y) from ?_, roofing (fun j=> - gamma j a b) f (fun i x hx=> Complex.ofRealCLM.contDiff.contDiffAt.comp x (h i x hx)) l x hx]; simp only [neg_mul, Finset.sum_neg_distrib]; congr 1; exact Finset.sum_congr rfl fun i _=>congr_arg _ (spiral open_away (grad i Green) (h i) l Complex.ofRealCLM x hx)
     simp_rw[neg_mul,sum_neg_distrib];rfl
noncomputable def spark (z:P):Spike:= ∑ a: SpaceAxis, ((thetaS (base a) z:ℝ):ℂ) • gamma a.castSucc
noncomputable def shine (t:ℝ)(z:P):Spike:= (t:ℂ) • gamma K - I₀ • spark z
lemma step_cont (l:List (Fin 3)): Continuous fun y:P=>stepTheta y l:=by induction l with| nil=> exact continuous_const| cons a l ih=> exact (show Continuous (fun y:P=>thetaS (base a) y*stepTheta y l) from (continuous_const.inner continuous_subtype_val).mul ih) |>.congr (by simp [stepTheta]) -- uncertain
lemma sparkG(j k :Pinor)(z:P): spark z j k=∑ a:Fin 3, ((thetaS (base a) z:ℝ):ℂ)*gamma a.castSucc j k:=by simp[spark,Matrix.sum_apply]
lemma shineG(j k:Pinor)(t:ℝ)(z:P): shine t z j k=t*gamma K j k-I₀* (spark z j k):=rfl
lemma shines (t:ℝ)(a b:Pinor): Continuous fun z:P=> shine t z a b:=by simp_rw[shineG,sparkG]; unfold thetaS; fun_prop
include hr hp he
lemma spinC (l : List (Fin 3))(a b:Pinor) : deriveL (toAxes l) (dirac a b) (prelude s) = (rayG r (l.length+1):ℂ) * I₀^l.length * (∫ y:P, (stepTheta y l:ℝ) * (shine t y a b) ∂Ω) :=by
      have hs:s≠0:=by intro hx; rw [hx,abs_zero] at hp; linarith
      rw [derived_res a b _ _ (swept s hs),Fin.sum_univ_castSucc]
      rw [show (↑(deriveL (toAxes l) (grad (Fin.last 3) Green) (prelude s)):ℂ)= _ from tGamma hr hp he l]
      let p:P→ℝ:= fun y=>stepTheta y l; let q:P→ℂ:=fun y=>p y; let v:ℂ:=rayG r (l.length+1); let J:=l.length
      let Q (i:SpaceAxis) :P→ℂ:=fun y=>stepTheta y (i::l)
      have h(i:SpaceAxis): (↑(deriveL (toAxes l) (grad i.castSucc Green) (prelude s)):ℂ)= v*I₀^(J+1)*(∫ y:P,Q i y ∂Ω):=by
            have hp':deriveL (toAxes l) (grad i.castSucc Green) (prelude s)=deriveL (toAxes (i::l)) Green (prelude s):=by
                 let j:=i.castSucc; let x:= prelude s; change deriveL (toAxes l) (deriveL [j] Green) x = _; rw [← lyras]; exact commute_a open_away Green (fun x h=>freeSmooth h) _ _ (List.perm_append_comm ..) x (swept s hs)
            rw [hp',spGamma hr hp]; refine congr_arg (v * I₀^(J+1)* ·) ?_; exact (integral_ofReal ..).symm
      simp_rw [h]; have hf : (↑(∫ y:P,stepTheta y l ∂Ω):ℂ)= (∫ y:P,q y ∂Ω):=(integral_ofReal ..).symm -- syntax
      rw[hf]
      let F(i:SpaceAxis)(y:P):= Q i y * gamma i.castSucc a b; let W:P→ℂ:=fun y=> q y * ((t:ℂ)*gamma K a b)
      have hg(y:P): ↑(stepTheta y l) * shine t y a b= W y-∑ i: Fin 3, I₀*F i y:=by
             rw [shineG,mul_sub,sparkG,mul_sum,mul_sum]; congr 1; refine sum_congr rfl fun i _=>?_ ; unfold F Q stepTheta; simp only [List.map_cons,List.prod_cons]; push_cast; ring
      have hu(i:Fin 3): Integrable (fun y:P=>I₀*F i y) Ω:= ((show Continuous _ from continuous_const.mul ((Complex.continuous_ofReal.comp (step_cont _)).mul continuous_const))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      simp_rw[hg]; rw[integral_sub,integral_finsetSum _ (fun i _=>hu i)];
      · unfold W F; simp_rw[integral_const_mul,integral_mul_const]; simp_rw[← mul_assoc]; rw [mul_sub, Finset.mul_sum,neg_add_rev,sub_eq_add_neg]; apply congr_arg₂ (· + ·)
        · push_cast; rw [show timeAxis=3 from rfl]; ring
        · congr 1; apply Finset.sum_congr rfl; intro i _; rw [pow_succ]; unfold v J; ring
      · exact ((show Continuous W from (Complex.continuous_ofReal.comp (step_cont l)).mul continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      exact integrable_finsetSum _ fun i _=> hu i
end YM.DawnS
