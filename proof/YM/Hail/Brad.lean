import YM.Hail.Daze
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
variable {d e k:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2) (t:List (letters k))(g:GPol)
local notation "w" => Points.direction (0:Fin 2) j
local notation "R" => Maxwell.reduceEq (G:=su)
variable (s q: letters d)
noncomputable def stood (s q: letters d)(t:List (letters k))(g:GPol)(x:Points 2) :ℂ:= ∑ i:Fin t.length, (-1:ℂ)^([q].length+i.val)*(canopy x 1 (R g))*(atP x s t[i])*(fan x [q] (t.eraseIdx i.val)) -- R macro tied x g? R only su
local notation "V"=> dual d k
include hx
lemma B_cost : V x ((1:GPol) ⊗ₜ[ℂ] tagD [s,q]) (g⊗ₜ[ℂ] tagD t)= stood s q t g x:=by
    rw[splitted x hx, ← sense]; change canopy x (R (1:GPol)) (R g)*fan x (s::q::[]) t= _; rw [map_one,hus x hx]; unfold stood; rw[Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=>by ring)
variable (S U Q T: letters e)
private lemma coastL (i:Fin t.length)(hz:ℂ):
     D w (fun x:Points 2=>hz*canopy x 1 (R g)*atP x s t[i]*fan x [q] (t.eraseIdx i.val)) x= hz * canopy x 1 (R g)*D w (fun x: Points 2 =>atP x s t[i]) x * fan x [q] (t.eraseIdx i.val)+ hz * canopy x 1 (R g)*atP x s t[i]* D w (fun x:Points 2=>fan x [q] (t.eraseIdx i.val)) x:=by
    let f:=fun x:Points 2=> hz*canopy x 1 (R g); let y:=fun x:Points 2=>atP x s t[i]; let A:=fun x:Points 2=>fan x [q] (t.eraseIdx i.val); have hf : DifferentiableAt ℝ f x:=(spell x hx g).const_mul _; have hu:DifferentiableAt ℝ y x:=at_s x hx ..; have hv:DifferentiableAt ℝ A x:=dawn_at x hx ..; have he : fderiv ℝ f x w=0:=by unfold f; rw[fderiv_const_mul (spell x hx g)]; change hz*D w _ x=0; rw[calm j x hx,mul_zero];
    change fderiv ℝ (fun x:Points 2=> f x*y x*A x) x w=f x * fderiv ℝ y x w *A x+ f x*y x*fderiv ℝ A x w; rw [fderiv_fun_mul (hf.fun_mul hu) hv]; change f x*y x*fderiv ℝ A x w+A x*fderiv ℝ (fun x:Points 2=>f x*y x) x w=_; rw [fderiv_fun_mul hf hu]; change f x*y x*fderiv ℝ A x w+A x*(f x*fderiv ℝ y x w+y x*fderiv ℝ f x w)=_; rw[he]; ring
open Finset
lemma cobby (hs:∀ (v:letters k),D w (fun z=>atP z s v) x=atP x S v)(ht:∀ u:List (letters k), D w (fun z=>fan z [q] u) x= fan x [Q] u)(hl:∀ v:List (letters k),fan x [q] v=fan x [U] v)(hk:∀ v:letters k,atP x s v=atP x T v) : rayL j x hx d k ((1:GPol) ⊗ₜ[ℂ] tagD [s,q]) (g⊗ₜ[ℂ] tagD t) = dual e k x (1⊗ₜ[ℂ] tagD [S,U]) (g⊗ₜ[ℂ] tagD t)+dual e k x (1⊗ₜ[ℂ] tagD [T,Q]) (g⊗ₜ[ℂ] tagD t):=by
    rw [D_ray]; have h: (fun x:Points 2=> V x ((1:GPol)⊗ₜ[ℂ] tagD [s,q]) (g⊗ₜ[ℂ] tagD t))=ᶠ[𝓝 x] stood s q t g:= (show ∀ᶠ z in 𝓝 x,z∈conf _ from (conf_open _).mem_nhds hx).mono fun z he=>B_cost z he t g s q
    rw [GermD w h, B_cost x hx, B_cost x hx]; unfold D stood; rw [fderiv_fun_sum]; rw [_root_.sum_apply, ← Finset.sum_add_distrib]; apply sum_congr rfl; intro i _; exact (coastL j x hx t g s q i ((-1:ℂ)^([q].length+i.val))).trans (by dsimp only[List.length_cons,List.length_nil]; rw [hs,ht,hk, hl])
    intro i _; exact (((spell x hx g).const_mul _).mul (at_s x hx s t[i])).mul (dawn_at x hx _ _)
variable (u v: Pinor)(A B A' B': Multi e)(p b':Multi d)(c:Hue)(z:Flavor 6)(F:Spike)
variable (hA: UV.power A=UV.power p)(hB: UV.power B=UV.power b')(he: UV.power A'=update (UV.power p) j (UV.power p j+1))(hk: UV.power B'=update (UV.power b') j (UV.power b' j+1))
noncomputable def pureV (p q:Multi d)(z:Flavor 6)(c:Hue)(u v:Pinor):SpinPol d:= bar ((p,u,c),z)*psi ((q,v,c),z)
include hA hB he hk
lemma grove : rayL j x hx d k ((1:GPol)⊗ₜ[ℂ] (bar ((p,u,c),z)*psi ((b',v,c),z)))= dual e k x ((1:GPol)⊗ₜ[ℂ](bar ((A',u,c),z)*psi ((B,v,c),z)))+ dual e k x ((1:GPol)⊗ₜ[ℂ](bar ((A,u,c),z)*psi ((B',v,c),z))):=by
    have h {d:ℕ}(p q:Multi d) :bar ((p,u,c),z)*psi ((q,v,c),z)=tagD [bt u c z p, cl v c z q]:=by rw[tagD,List.map_cons,List.map_singleton,List.prod_cons,List.prod_singleton]; rfl
    rw[h,h,h]; apply (basisU k).ext; intro w'; rw [sweet x hx]; exact cobby j x hx _ _ _ _ _ _ _ _ (fun y=> rimCall j x hx u c z y p A' he) (fun y=> twin j x hx y (cl v c z b') (cl v c z B') (fun y=> rimY j x hx v c z y b' B' hk)) (fun y=>(rim_unit x hx y v c z b' B hB).symm) (fun y=> (rimJ x hx u c z y p A hA).symm) -- Kindle signature
lemma tenureD :rayL j x hx d k (bilinear z z F p b')=dual e k x (bilinear z z F A' B)+dual e k x (bilinear z z F A B'):=by
     unfold bilinear; simp_rw[TensorProduct.tmul_sum,TensorProduct.tmul_smul,map_sum,map_smul]; simp_rw [fun u v c=> grove (k:=k) j x hx u v A B A' B' p b' c z hA hB he hk, smul_add,sum_add_distrib]
end YM.Hail
#print axioms YM.Hail.tenureD
