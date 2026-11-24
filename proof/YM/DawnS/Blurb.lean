import YM.DawnS.Plinth
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor Maxwell Arise.Range
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct
local notation "Y"=>Vertex
local notation "P"=>RingS
local notation "B"=>basis timeAxis
local notation "Ω"=>muS
local notation "I₀"=>Complex.I
local notation "DΓ"=> Arise.Range.deriveL
variable {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U]
local notation "T₀"=> (timeAxis:Axis)
-- list insertion representation
lemma unJet(f:E4→U)(hf:∀ x∈away,ContDiffAt ℝ ∞ f x)(l:List Axis)(x:E4)(hx:x∈away): deriveL l f x=iteratedFDeriv ℝ l.length f x (basis∘l.get):=by
    rw[probeL l f open_away hf x hx,Tensor.coeff,← Nat.cast_smul_eq_nsmul ℝ,ContinuousMultilinearMap.smul_apply,smul_smul,mul_inv_cancel₀ (by positivity),one_smul] -- fix reverse
noncomputable abbrev toAxes (l:List (Fin 3)):List Axis:=l.map Fin.castSucc
lemma spact(f:E4→U)(hf:∀ x∈away,ContDiffAt ℝ ∞ f x)(l:List SpaceAxis)(x:E4)(hx:x∈away):deriveL (toAxes l) f x =fromAir l.length f x (base∘l.get):=by
     rw [unJet f hf _ _ hx]; let p:= toAxes l
     have he : p.length=l.length:=by simp[p,toAxes]
     let g:=fun i:Fin l.length=> basis ((l.get i).castSucc)
     change iteratedFDeriv ℝ p.length f x _=iteratedFDeriv ℝ l.length f x (fun i=> align (base (l.get i))); simp_rw[align_base]
     suffices h:(basis∘ p.get)=g ∘ Fin.cast he by rw[h]; clear h; generalize p.length=n at *; subst n; rfl
     ext1 i; simp [p,toAxes,g]
noncomputable def stepTheta(z:P)(l:List (Fin 3)):ℝ:=(l.map (fun i=>thetaS (base i) z)).prod
lemma storm (l:List (Fin 3)) : wheel l.length (base∘l.get) =∫ z:P,stepTheta z l ∂Ω:=by
     apply integral_congr_ae; refine Eventually.of_forall fun z=>?_; unfold stepTheta; change ∏ i:Fin l.length, thetaS (base (l.get i)) z = _; let f(i:SpaceAxis):=thetaS (base i) z; change _=(l.map f).prod; rw [show l.map f=(List.ofFn (f ∘ l.get)) from (by rw[←List.map_ofFn,List.ofFn_get]),List.prod_ofFn]; rfl -- mismatch
lemma stepTheta_g (z:P)(x y : List (Fin 3)): stepTheta z (x++y)=stepTheta z x*stepTheta z y:=by simp [stepTheta]
variable {r s t:ℝ}(hr:0<r)(hp:|s|=r)(he:s=t*r)
include hr hp
lemma spGamma(l:List (Fin 3)): (↑(deriveL (toAxes l) Green (prelude s)) : ℂ) = rayG r l.length * I₀^l.length * ↑(∫ y:P, stepTheta y l ∂Ω):=by
     have hs:s≠0:=by intro hx; rw[hx,abs_zero] at hp; linarith
     subst r; rw [spact _ (fun x hx=>freeSmooth hx) _ _ (swept s hs),windC hs,storm]
include he
lemma tGamma(l:List (Fin 3)): (↑(deriveL (toAxes l) (grad T₀ Green) (prelude s)) : ℂ) = (rayG r (l.length+1):ℝ) * (-t:ℝ)* I₀^l.length * ↑(∫ y:P, stepTheta y l ∂Ω):=by
     have hs:s≠0:=by intro hx; rw[hx,abs_zero] at hp; linarith
     rw [spact _ (fun x hx=>gradGradientSmooth hx _) _ _ (swept s hs),waterC _ _ _ hr hp he,storm]
end YM.DawnS
