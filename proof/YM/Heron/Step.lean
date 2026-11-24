import YM.Heron.Airs
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
variable (A:TinG)(i j k:Axis)
local notation "Q"=>Faces
open Maxwell (grad)
noncomputable def dotL : Q→L[ℝ] Q→L[ℝ]ℂ:= LinearMap.toContinuousLinearMap
    { toFun:=fun x=> (LinearMap.toContinuousLinearMap {toFun:=fun y=> x ⬝ᵥ y,map_add':=dotProduct_add x,map_smul':=fun a y=>dotProduct_smul a x y}: Q→L[ℝ]ℂ), map_add':=fun x y=>ContinuousLinearMap.ext fun z=> add_dotProduct x y z, map_smul':=fun a x=>ContinuousLinearMap.ext fun y=>smul_dotProduct a x y }
local notation "D°"=>dotL
variable (f g:Spins)(x:E4)(hf: ContDiffAt ℝ ∞ f x)(hg:ContDiffAt ℝ ∞ g x)
lemma bore (x y:Q): D° x y=x ⬝ᵥ y:=rfl
include hf hg
lemma hot : ContDiffAt ℝ ∞ (fun y:E4=>dotL (f y) (g y)) x:= (dotL.contDiff.contDiffAt.comp x hf).clm_apply hg
lemma trapped : grad i (fun y:E4=>dotL (f y) (g y)) x= dotL (grad i f x) (g x)+dotL (f x) (grad i g x):=by
      let F:=dotL ∘ f; have h:= (dotL.differentiableAt.comp x (hf.differentiableAt (by simp))).hasFDerivAt.clm_apply (hg.differentiableAt (by simp)).hasFDerivAt; change fderiv ℝ (fun y=>F y (g y)) x _= _; rw[h.fderiv]; change F x (grad i g x) + grad i F x (g x)= _; unfold F; rw[Maxwell.grad_linear D° hf i]; exact add_comm ..
local notation "K"=> cog A
noncomputable def streak (i j:Axis)(x:E4):ℂ:= dotL (f x) (K i (grad j g x))-dotL (grad j f x) (K i (g x))
local notation "P"=> streak A f g
lemma way_a : ContDiffAt ℝ ∞ (P i j) x:= ContDiffAt.sub (hot f (cog A i ∘ grad j g) x hf ((K i).contDiff.contDiffAt.comp x (Maxwell.grad_smooth j hg (by simp)))) (hot (grad j f) (cog A i ∘ g) x (Maxwell.grad_smooth j hf (by simp)) ((K i).contDiff.contDiffAt.comp x hg))
local notation "B"=> FlipT A
local notation "E"=> enD A
local notation "L"=> enD B
lemma trappedK : grad k (P i j) x =
  (D° (grad k f x) (K i (grad j g x))+D° (f x) (K i (grad k (grad j g) x)))-(D° (grad k (grad j f) x) (K i (g x))+D° (grad j f x) (K i (grad k g x))):=by
     let hp:= Maxwell.grad_smooth j (m:=∞) hf (by simp); let hs:= Maxwell.grad_smooth j (m:=∞) hg (by simp); let F:= cog A i; let U:= F ∘ g; let V:= F ∘ (grad j g); have hU:ContDiffAt ℝ ∞ U x:= F.contDiff.contDiffAt.comp x hg; have hV: ContDiffAt ℝ ∞ V x:= F.contDiff.contDiffAt.comp x hs
     let v: E4→ℂ:=fun x=> dotL (f x) (V x); let u:E4→ℂ:=fun x=>dotL (grad j f x) (U x);
     change grad k (v-u) x=_; rw [grad_dif ((hot f V x hf hV).differentiableAt (by simp)) ((hot (grad j f) U x hp hU).differentiableAt (by simp)), show grad k v x=_ from trapped k f V x hf hV, show grad k u x=_ from trapped k (grad j f) U x hp hU]; unfold U V; rw[Maxwell.grad_linear F hs k,Maxwell.grad_linear F hg k]; rfl
lemma Stiff : ∑ i:Axis,grad i (P i j) x= D° (L f x) (grad j g x)+ D° (f x) (grad j (E g) x)- (D° (grad j (L f) x) (g x)+ D° (grad j f x) (E g x)):=by
    have hp(i j:Axis) : grad i (grad j f) x = grad j (grad i f) x:=Maxwell.grad_comm (hf.of_le (WithTop.coe_le_coe.mpr le_top)) i j
    have hs(i j:Axis) : grad i (grad j g) x=grad j (grad i g) x:=Maxwell.grad_comm (hg.of_le (WithTop.coe_le_coe.mpr le_top)) i j
    simp_rw [trappedK A _ _ _ _ _ _ hf hg]; rw [rose A j g hg , rose B j f hf];
    simp only[enD, bore,sum_dotProduct,dotProduct_sum,flip_mul, Finset.sum_sub_distrib,Finset.sum_add_distrib]; simp_rw [fun i=> hp i j, fun i=> hs i j]
lemma motion : ∑ i:Axis,grad i (P j i) x = D° (f x) (K j (∑ i:Axis,grad i (grad i g) x)) - D° (∑ i:Axis,grad i (grad i f) x) (K j (g x)):=by
    simp_rw [trappedK A _ _ _ _ _ _ hf hg, _root_.map_sum, ContinuousLinearMap.sum_apply,Finset.sum_sub_distrib, Finset.sum_add_distrib]; abel
end YM.Heron
#print axioms YM.Heron.Stiff
#print axioms YM.Heron.motion
