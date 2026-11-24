import YM.Hail.Reap
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
variable {d e k:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2) (t:List (letters k))(g h:GPol)
open StressFlux (pair pairDeriv curl0 curl1)
-- scalar insertion at either. Maxwell glide kills. objective ray on these.
local notation "pΔ" => Points.direction (0:Fin 2) j
local notation "Q" => Maxwell.Wick.moment su
local notation "R" => Maxwell.reduceEq (G:=su)
noncomputable def canopy (x:Points 2): Maxwell.WickPol su→ₗ[ℂ] Maxwell.WickPol su →ₗ[ℂ] ℂ:=
 { toFun:=fun f=> (Q x).toLinearMap (![f,0]) 1, map_add':=by
       intro p q; apply LinearMap.ext; intro r; change Q x (update _ _ _)=Q x (update _ _ _)+Q x (update _ _ _); have h (f s:Maxwell.WickPol su):update (![f,0]) (1:Fin 2) s=update (![0,s]) 0 f:=by funext i;fin_cases i <;> simp
       rw[h,h,h]; exact MultilinearMap.map_update_add ..,
   map_smul':=by
       intro z p; apply LinearMap.ext; intro r; change Q x (update _ _ _)=z*Q x (update _ _ _); have h(f s:Maxwell.WickPol su): update (![f,0]) (1: Fin 2) s=update (![0,s]) 0 f:=by funext i; fin_cases i<;>simp
       rw[h,h,(Q x).map_update_smul]; rfl }
local notation "T"=> canopy
lemma sense (f r:Maxwell.WickPol su): T x f r= Q x (![f,r]):=by
     change Q x (update _ 1 _)=_; apply congr_arg; funext i; fin_cases i<;>simp
include hx
lemma clearT (f r:Maxwell.WickPol su): D pΔ (fun x:Points 2=>T x f r) x=T x ((Maxwell.Free.rewired (Maxwell.Free.glide su (basis j))) f) r:=by
     simp only [sense]; have ht:= Maxwell.Free.positionD (![f,r]) hx (0:Fin 2) j; refine ht.trans ?_; apply congr_arg; funext i; fin_cases i<;>simp
noncomputable def lit (t:List (letters k)):ℂ:= if t = [] then 1 else 0
lemma tintT (t:List (letters k))(P:ℕ) : fan (d:=P) x [] t=lit t:=by
     cases t with| nil=>exact emptyS x hx| cons a t=> simpa [lit] using (tailV (d:=P) x hx t a)
lemma fireT (v:GPol)(r:ℕ) : dual r k x (v⊗ₜ[ℂ] 1) (g⊗ₜ[ℂ] tagD t)=T x (R v) (R g) * lit t:=by rw[splitted x hx,← sense]; exact congr_arg (_*·) (tintT x hx t r)
lemma litD (v:GPol)(r:ℕ): rayL j x hx r k (v⊗ₜ[ℂ] 1) (g⊗ₜ[ℂ] tagD t)= T x ((Maxwell.Free.rewired (Maxwell.Free.glide su (basis j))) (R v)) (R g) * lit t:=by
    rw [D_ray]; rw[GermD pΔ (show (fun x:Points 2=>dual r k x (v⊗ₜ[ℂ] 1) (g⊗ₜ[ℂ] tagD t))=ᶠ[𝓝 x] (fun x:Points 2=>T x (R v) (R g)*lit t) from (show ∀ᶠ y in 𝓝 x,y∈conf _ from (conf_open _).mem_nhds hx).mono fun x hx=>fireT x hx t g v r),← clearT j x hx]; unfold Analysis.D; rw [fderiv_mul_const]; exact mul_comm .. -- maybe one goal
    simp only[sense]; exact (Maxwell.Wick.moment_smooth _ hx).differentiableAt (by simp)
lemma emptyD : rayL j x hx d k (UV.unit d)=0:=by -- lint implicit syntax
     apply (basisU k).ext; intro v; rw [sweet x hx]; let m:GPol:= MvPolynomial.monomial v.1 1; change rayL j x hx d k ((1:GPol)⊗ₜ[ℂ] 1) _=0; rw[litD]; simp
lemma pair_Diff :
     rayL j x hx d k ((StressFlux.pair su a i b l).val⊗ₜ[ℂ] 1)= dual e k x ((pairDeriv su a i j b l).val⊗ₜ[ℂ]1)+dual e k x ((pairDeriv su b l j a i).val⊗ₜ[ℂ]1):=by
     apply (basisU k).ext; intro v; rw [sweet x hx]; simp only [litD j x hx,LinearMap.add_apply,fireT x hx]; rw[cutL,map_add,LinearMap.add_apply,add_mul]
end YM.Hail
#print axioms YM.Hail.emptyD
#print axioms YM.Hail.pair_Diff
