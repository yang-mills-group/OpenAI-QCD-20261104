import YM.DawnS.Rail
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
variable {d:ℕ}(r:ℝ)(hr:0<r)
local notation "I₀"=> Vault d
local notation "wd"=>fun _ : Fin 2 =>d
local notation "Q"=> chime (fun _ : Fin 2=>d) (dotsG r)
local notation "QZ"=>unionB Q
local notation "K"=> timeAxis
open Maxwell.Free
local notation "A"=> Signed.reflect timeAxis
variable (C:Matrix (Vault d) (Vault d) ℂ)(hc:IsUnit C)(he:Cᴴ*hank d r*C=1)
include hc
lemma straw(x:wedgeR d):∃ y:Alg (Vault d), bareT d (swell C y)=x:=by
     obtain ⟨T,hT⟩:= (lofty C hc |> fun h => ((slashEq d).mkQ.comp (vaultT C)).exists_rightInverse_of_surjective h) -- usage range top
     refine ⟨ExteriorAlgebra.map T x,?_⟩
     unfold bareT swell; rw [← AlgHom.comp_apply _ (ExteriorAlgebra.map T),ExteriorAlgebra.map_comp_map,← AlgHom.comp_apply,ExteriorAlgebra.map_comp_map,←LinearMap.comp_assoc,hT]; simp -- unsure order
-- express tensor reppet
lemma exposeS(x:Pol d):∃ y: Finset (Vault d)→ UV.GPol,UV.Free.reduceEq x=UV.Free.reduceEq (∑ i,y i ⊗ₜ[ℂ] (swell C (Grass.mono i))):=by
      induction x using TensorProduct.induction_on with
      | zero=> exact ⟨fun _=>0,by simp⟩
      | add x y hx hy=> obtain ⟨v,hv⟩:=hx; obtain ⟨w,hw⟩:=hy; exact ⟨v+w,by rw [map_add,hv,hw, ←map_add,←sum_add_distrib]; apply congr_arg; refine sum_congr rfl fun i _=>?_ ; rw[Pi.add_apply,add_tmul]⟩
      | tmul x y=>
          obtain ⟨t,h⟩:=straw C hc (bareT d y); refine ⟨fun i=> Grass.coef i t • x,?_⟩; let X:=Maxwell.reduceEq x; change Maxwell.reduceEq x ⊗ₜ[ℂ] bareT d y= _; rw[←h]; conv_lhs=> rw[← Grass.write t]
          simp_rw[map_sum,map_smul];
          rw [tmul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [UV.Free.reduceEq,TensorProduct.map_tmul,map_smul]; exact (smul_tmul _ _ _).symm
omit hc
include hr he
noncomputable abbrev apex (x y:Pol d):=UV.Free.moment wd (dotsG r) ![UV.adj K x,y]
lemma crossG (x y:GPol)(s t:Finset (Vault d)): apex r (x⊗ₜ[ℂ] swell C (Grass.mono s)) (y⊗ₜ[ℂ] swell C (Grass.mono t))=if s=t then score K (prelude (r/2)) (Maxwell.reduceEq x) (Maxwell.reduceEq y) else 0:=by
    unfold apex UV.adj; rw [TensorProduct.map_tmul]; let V:=((Labels.rotated A).toLinearMap.comp conjGPol) x; let p:= Wp (swell C (Grass.mono s)); let a:= τSpin _ (swell C (Grass.mono s)); let b:= swell C (Grass.mono t); let F:=![V,y]; let G:=![a,b];
    have hz : UV.Free.moment wd (dotsG r) ![V⊗ₜ[ℂ] a,y⊗ₜ[ℂ] b]= UV.Free.moment wd (dotsG r) (fun i:Fin 2=>F i⊗ₜ[ℂ] G i) := congr_arg _ (funext fun i=>by fin_cases i<;>rfl)
    change UV.Free.moment wd (dotsG r) ![V⊗ₜ[ℂ] a,y⊗ₜ[ℂ] b]=_; rw [hz,stroll (dotsG r) (distinct r hr)]; rw [show (fun i=> Maxwell.reduceEq (F i))= ![mirrorBar A (Maxwell.reduceEq x),Maxwell.reduceEq y] from ?h]; swap; · ext1 i; fin_cases i; exact gaugeC x; rfl
    rw [detectsG r hr]; rw[show (List.ofFn (fun i=> twig wd i (G i))).prod=p*Hp b from ?h2]; swap; · simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]; rfl
    rw [eclipse r hr C he]; split<;> simp
end YM.DawnS
#print axioms YM.DawnS.crossG
