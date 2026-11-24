import YM.Hail.Brad
import YM.Hail.Mena
import YM.Tawny.Velo
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
open Massive.Tawny Massive.Tawny.Cast Perla Perla.Fore Carnal Rays TableT Drill
open Finset Module LinearMap
variable {d e k:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2)(f:Flavor 6)
local notation "P"=> (0:Multi 8)
local notation "Z"=> (0:Multi 10)
local notation "cK"=> rayL j x hx 8 d
local notation "V"=> dual 10 d x
local notation "η"=>leadR
local notation "Y"=>ηR
private lemma stemP :power Z=power P:=rfl
lemma stemR :power (η a)=power (UV.first a):=by funext i; unfold power leadR UV.first; by_cases h:i=a ; subst i; simp; simp [h,Ne.symm h]
lemma stew :power (Y a j)= update (power (UV.first a)) j (power (UV.first a) j+1):=by rw [←stemR]; rfl
local notation "Spice"=> bilinear f f
lemma massD : gale (d:=d) x hx (scalarS f) j= V ((bee f).val j).val:=by
    rw[bee_val,beta_up]; unfold gale; simp_rw [W_mass]; rw [sum_eq_single j (?_) (by simp)]; rw [if_pos rfl]; change rayL j x hx 8 d (Spice 1 P P)=_; rw[tenureD (k:=d) j x hx Z Z (η j) (η j) P P f _ rfl rfl (add_zeroL _) (add_zeroL _),map_add,add_comm]
    intro i _ h; rw [if_neg h]; exact map_zero _
lemma alterD :
    cK (alter f a b).val= V (Spice (gamma a) Z (Y b j)-Spice (gamma a) (Y b j) Z)+ V (Spice (gamma a) (η j) (η b)-Spice (gamma a) (η b) (η j)):=by
    rw [amt]; unfold spinStressUnsymm; rw [map_sub,tenureD (k:=d) j x hx Z (η b) (η j) (Y b j) P (UV.first b) f _ rfl (stemR b) (add_zeroL _) (stew b j),tenureD (k:=d) j x hx (η b) Z (Y b j) (η j) (UV.first b) P f _ (stemR b) rfl (stew b j) (add_zeroL _),map_sub,map_sub]; abel
lemma alterL : cK (alter f j b).val= V (shell1 f b j).val+V (shell2 f b j).val:=by rw[alterD,shell1,shell2,basil_pond,basil_pond]
lemma alterR : cK (alter f b j).val=V (shell0 f b j).val:=by rw [alterD,shell0,basil_pond,sub_self,map_zero,add_zero]
include hx
lemma vanish (v:Label e)(h:projection v=0):dual e d x v.val=0:=by
    apply LinearMap.ext; intro p; change dual e d x v.val p=0; rw[valD]; have he:= congr_arg Subtype.val h; let u:=petals (A:=Pol) (0:Pol e) p; have ht:moment (![e,d]) x u=0:=MultilinearMap.map_coord_zero _ 0 rfl
    refine Eq.trans (descendant x hx _ u ?_) ht; intro i; fin_cases i; exact Eq.trans he (map_zero _).symm; rfl
lemma sunL : gale (d:=d) x hx (sunS f) j=0:=by
   unfold gale; simp_rw[W_sun,Submodule.coe_add,map_add, show ∀ k,rayL k x hx 8 d (alter f k j).val=_ from fun k=>alterL j k x hx f, show ∀ k,rayL k x hx 8 d (alter f j k).val=_ from fun k=>alterR j k x hx f] -- order
   rw [sum_add_distrib, sum_add_distrib]; have h0:= tax_and f
   have ht:∀ (F:Axis→Label 10)(z:RawVec 10), z.val j=∑ i:Axis,F i→ symbV z=0→ ∑ i:Axis,V (F i).val=0:=by
       intro F z hz h; have hu: projection (z.val j)=0:= congr_fun h j; rw [hz] at hu; have hv:= vanish (d:=d) x hx _ hu; simp_rw [AddSubmonoidClass.coe_finsetSum,map_sum] at hv; exact hv
   rw [ht _ (lapL f) rfl h0.1, ht _ (slashT f) rfl h0.2.2.2.1,ht _ (slashS f) rfl h0.2.2.1,add_zero,add_zero]
lemma diagL :gale (d:=d) x hx (wingS f) j=(2:ℂ) • V ((lup f).val j).val:=by
   unfold gale; simp_rw[W_wing]; rw [sum_eq_single j (?_) (by simp)]; rw[if_pos rfl,W_sun]; simp only[Submodule.coe_add,map_add,two_smul, lup_val]; rw [alterR]
   intro i _ h; rw[if_neg h]; exact map_zero _
lemma nullD (v:Label e)(h:projection v=0):rayL j x hx e d v.val=0:=by
   apply LinearMap.ext; intro w'; change rayL _ x hx _ d _ _=0; rw [D_ray]; have hP:(fun z: Points 2 => dual e d z v.val w')=ᶠ[𝓝 x] fun _=> (0:ℂ):=(show ∀ᶠ z in 𝓝 x,z∈conf _ from (conf_open _).mem_nhds hx).mono fun z hz=> DFunLike.congr_fun (vanish z hz v h) w'; rw[GermD _ hP]; simp[D]
lemma veinL : gale (d:=d) x hx (traceT f) j=0:=by unfold gale; apply Finset.sum_eq_zero; intro _ _; exact nullD _ x hx _ (congr_fun (simplify_s f) _)
end YM.Hail
#print axioms YM.Hail.veinL
#print axioms YM.Hail.diagL
#print axioms YM.Hail.sunL
#print axioms YM.Hail.massD
