import YM.Hail.Ruby
import YM.Hail.Dyke
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
variable {d e k:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2) (t:List (letters k))(g:GPol)(u v:Pinor)(c:Hue)(r:Flavor 6)
local notation "w" => Points.direction (0:Fin 2) j
noncomputable def cloud (s:letters d)(t:List (letters k))(x: Points 2):ℂ:=∑ i:Fin t.length, ((-1:ℂ)^i.val * lit (t.eraseIdx i.val))*atP x s t[i]
local notation "R" => Maxwell.reduceEq (G:=su)
local notation "P"=> Pol (d+2)
noncomputable def cl (p:Multi d):letters d:= Sum.inl ((p,u,c),r)
noncomputable def bt (p:Multi d):letters d:= Sum.inr ((p,u,c),r)
local notation "U"=> bt u c r
local notation "Z"=> cl v c r
variable (s:letters d)(s':letters e)(y:letters k)
include hx
lemma at_s (u:letters d)(v:letters k): DifferentiableAt ℝ (fun x:Points 2=>atP x u v) x :=(Sip.puff hx (![d,k]) (⟨0,u⟩) (⟨1,v⟩)).differentiableAt (by simp)
local notation "cK"=> canopy x 1 (R g)
lemma calm : D w (fun x:Points 2=> canopy x 1 (R g)) x=0:=by rw [clearT]; simp; exact hx
lemma spell : DifferentiableAt ℝ (fun x:Points 2=> canopy x 1 (R g)) x:=by simp only[sense]; exact (Maxwell.Wick.moment_smooth _ hx).differentiableAt (by simp)
lemma kindle : fan x [s] t=∑ i:Fin t.length, (-1:ℂ)^i.val*atP x s t[i]*lit (t.eraseIdx i.val):=by
     rw[hus x hx]; apply Finset.sum_congr rfl; intro i _; rw [tintT x hx]; simp
private lemma sunrise (v:Fin t.length):(-1:ℂ)^v.val * atP x s t[v] * lit (t.eraseIdx v.val)=(-1:ℂ)^v.val * atP x s t[v] * lit (t.eraseIdx v.val):=rfl
-- use germ lemmas calc. helper arbitrary tail constants
open scoped Topology
lemma cloud_at :cloud s t x=fan x [s] t:=by rw[kindle x hx]; unfold cloud; exact Finset.sum_congr rfl fun i _=>by ring
lemma dawn_at : DifferentiableAt ℝ (fun z:Points 2=>fan z [s] t) x:=by
    have he: DifferentiableAt ℝ (cloud s t) x:= DifferentiableAt.fun_sum fun i _=> (at_s x hx _ _).const_mul _
    apply he.congr_of_eventuallyEq; exact (show ∀ᶠ y in 𝓝 x,y∈conf _ from (conf_open _).mem_nhds hx).mono fun y hy=> (cloud_at y hy t s).symm
lemma twin (he:∀ y:letters k,D w (fun x:Points 2=>atP x s y) x=atP x s' y): D w (fun z:Points 2=>fan z [s] t) x=fan x [s'] t:=by
    have h:(fun z:Points 2=>fan z [s] t)=ᶠ[𝓝 x] cloud s t:=(show ∀ᶠ y in 𝓝 x,y∈conf _ from (conf_open _).mem_nhds hx).mono fun y hy=>(cloud_at y hy t s).symm; rw[GermD w h,← cloud_at x hx]; unfold cloud D; rw[fderiv_fun_sum]; rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw[fderiv_const_mul (at_s x hx _ _)]; exact congr_arg (_*·) (he _)
    intro i _; exact (at_s x hx _ _).const_mul _
variable (p q:Multi d)(P' Q B A: Multi e)
lemma rimJ (h: UV.power A=UV.power p): atP x (bt u c r A) y=atP x (bt u c r p) y:=by
   rcases y with y|y
   · change -leg y ((A,u,c),r) (x 1) (x 0)= -leg y ((p,u,c),r) _ _; unfold leg; simp only [step_eq A p h]
   rfl
lemma rimK(h: UV.power B=UV.power q): atP x (cl v c r B) y= atP x (cl v c r q) y:=by
    cases y with
    | inl y=>rfl
    | inr y=> change leg ((B,v,c),r) y (x 0) (x 1)=leg ((q,v,c),r) y _ _; unfold leg; simp only [step_eq B q h]
lemma rimCall(h: UV.power P'=update (UV.power p) j (UV.power p j+1)) : D w (fun z=>atP z (bt u c r p) y) x= atP x (bt u c r P') y:=by
    rcases y with y|y
    · change D w (fun z=> -leg y ((p,u,c),r) (z 1) (z 0)) x= -_; rw [Analysis.D,fderiv_fun_neg]; · exact congr_arg Neg.neg (after_leg j x hx p P' y u c r h)
    change D w (fun _=> (0:ℂ)) x=0; simp [Analysis.D]
lemma rimY(h: UV.power Q=update (UV.power q) j (UV.power q j+1)) : D w (fun z=>atP z (cl v c r q) y) x=atP x (cl v c r Q) y:=by
    rcases y with y|y; · change D w (fun _=> (0:ℂ)) x=0; simp [Analysis.D]
    exact over_leg j x hx q Q _ v c r h -- syntax
lemma rim_unit(h: UV.power B=UV.power q): fan x [cl v c r B] t=fan x [cl v c r q] t:=by rw[← cloud_at x hx,← cloud_at x hx]; simp only[cloud,fun y=>rimK x hx v c r y q B h]
end YM.Hail
#print axioms YM.Hail.twin
#print axioms YM.Hail.rim_unit
