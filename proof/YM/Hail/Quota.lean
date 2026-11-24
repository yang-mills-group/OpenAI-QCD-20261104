import YM.Hail.Purl
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical ComplexOrder
open Massive.Tawny Massive.Tawny.Cast Perla Perla.Fore Carnal Rays TableT Drill
open Finset Module LinearMap
variable {d e k:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2)(f:Flavor 6)(r:Flavor 6→Fin 4→ℂ)(p:Fin 4→ℂ)
local notation "V"=> dual 10 d x
local notation "Sx"=> RawTensor 1 8
local notation "H"=> symbS 1
noncomputable def hydra (r: Values 4) : Values 7:= fun i=>![r i 0,0,2*r i 2,0,0,0,0]
noncomputable def striga (p:Fin 4→ℂ): Fin 3→ℂ:=![2*p 2,(1/2:ℂ)*p 1+2*p 3,0]
lemma galeL : ∃ L:Sx→ₗ[ℂ]( Axis→(Pol d →ₗ[ℂ] ℂ)), ∀ t,L t=gale x hx t:=by
    let F(k a:Axis): Sx →ₗ[ℂ] Pol d →ₗ[ℂ]ℂ:= rayL k x hx 8 d ∘ₗ (UV.labels 8).subtype ∘ₗ proj (k,a) ∘ₗ (RawTensor 1 8).subtype; exact ⟨LinearMap.pi (fun a:Axis=>∑ k:Axis,F k a), fun t=> funext fun a=>by change (∑ k:Axis,F k a) t= _; rw[LinearMap.sum_apply]; rfl⟩
lemma soloL : gale (d:=d) x hx (axisσ f (r f)) j= V (((vectorZ f (hydra r f)).val j).val):=by
   obtain ⟨L,h⟩:=galeL (d:=d) x hx; unfold axisσ; rw[←h]; simp only[_root_.map_add,_root_.map_smul,Pi.add_apply,Pi.smul_apply]; simp only[h,massD,diagL,sunL,veinL,smul_zero,add_zero]; unfold vectorZ; simp only [hydra,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply, Pi.smul_apply,_root_.map_add,_root_.map_smul]; dsimp only[Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ, Fin.reduceSucc,Matrix.cons_val_fin_one] -- use change
   simp; module
lemma stageL : gale (d:=d) x hx (gaugeσ p) j=V (((ocean (striga p)).val j).val):=by
   obtain ⟨L,h⟩:=galeL (d:=d) x hx; unfold gaugeσ; rw [←h]; simp only [_root_.map_add,_root_.map_smul,Pi.add_apply,Pi.smul_apply]; simp only [h,darkD,haloD,gale_at,spire_D]; have he:V (eulerV.val j).val=0:= vanish x hx _ (congr_fun (tax_and (0:Flavor 6)).2.2.2.2 j); unfold ocean; simp only[Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,_root_.map_add,_root_.map_smul]; simp only [he, Pi.zero_apply]; unfold striga; dsimp only[Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.reduceSucc]; module
lemma pollen : gale (d:=d) x hx (poseσ (r,p)) j= V (((plaza (hydra r,striga p)).val j).val):=by
    obtain ⟨L,h⟩:=galeL (d:=d) x hx; change _= V (((vectorY _+ ocean _).val _).val); rw [← h, show poseσ (r,p)= poseσT r+gaugeσ p from rfl]; simp only[poseσT,_root_.map_add,_root_.map_sum, Pi.add_apply,Finset.sum_apply, Submodule.coe_add,vectorY,AddSubmonoidClass.coe_finsetSum]; simp only[h,Finset.sum_apply,soloL,stageL]
-- turns bilinear from second slot > use Ward convergence for derivative at second instead! faith requires adj first. could take probe v_s at x mirrored p such that sym adj=v, if projection 0 argument needs projection adj? If v projection nonzero but adj=v*, maybe adj preserves via RawSym? Show if vanish first v then take x as adj(i) v; probe adj nonzero because tensor cov and C-even yields charge.B if v complex. alternatively swapping proof
lemma wellness (u:Label d)(t:Label d):dual d d x u.val t.val=UV.Free.wick (fun _:Fin 2=>d) x (![u,t]):=by
   rw[valD]; let g:Fin 2→ℕ:=![d,d]; let f:Fin 2→ℕ:=fun _=>d; let F:= petals (A:=Pol) u.val t.val; let G:=fun i:Fin 2=>(![u,t] i).val; change moment g x F= moment f x G; have ht:g=f:=by funext i; fin_cases i<;>rfl
   have hc(v w:Fin 2→ℕ)(hv:v=w)(p:(i:Fin 2)→Pol (v i))(q:(i:Fin 2)→Pol (w i))(h:∀ i:Fin 2,HEq (p i) (q i)):moment v x p=moment w x q:=by
       subst w; rw [show p=q from funext fun i=>eq_of_heq (h i)]
   exact hc g f ht F G (fun i=>by fin_cases i<;> exact HEq.rfl)
end YM.Hail
#print axioms YM.Hail.pollen
