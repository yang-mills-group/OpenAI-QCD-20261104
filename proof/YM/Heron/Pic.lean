import YM.Heron.Lum
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad)
variable (A:TinG)(hc:TrueC A)(i j k:Axis)(p:E4)(D₀:Faces){U:Set E4}(hp:p∈U)(g:Spins)(v:Drive)(χ:E4→ℝ)(hw:Way A U g)(hv:Seam v)(hs:χ=ᶠ[𝓝 p]fun _=>1)
local notation "V"=> aura v g χ D₀
local notation "Y"=>tiers A v g χ D₀
local notation "M"=>vale A v g χ D₀
local notation "R"=>dotL
local notation "G"=> cog A
include hs
lemma auraP :V p=∑ j:Axis,v j p • R D₀ (grad j g p):=by unfold aura; simp only [show χ p=1 from hs.self_of_nhds, one_mul]
include hv
lemma steers : grad i (v i) p=0:=by have h:=hv.skew p i i; linarith
include hw hp
lemma yarn : grad i (Y i) p = v i p • R D₀ (grad i g p)+(∑ j:Axis, (grad i (v j) p • R D₀ (G i (G j (g p)))+ v j p • R D₀ (G i (G j (grad i g p))))):=by
    let F:=fun y=> v i y • R D₀ (g y); let W(j:Axis):= (dotL D₀) ∘L (cog A i) ∘L (cog A j); let H(j:Axis)(y:E4):= v j y • W j (g y); have ht:Y i=ᶠ[𝓝 p] fun y=> F y + ∑ j:Axis,H j y:= by filter_upwards [hs] with x hx; simp only [tiers,show χ x=1 from hx,one_mul]; rfl
    have he:DifferentiableAt ℝ g p:=(hw.live _ hp).differentiableAt (by simp); have hv'(i): DifferentiableAt ℝ (v i) p:=(hv.smooth i).differentiable (by simp) p; have hF:DifferentiableAt ℝ F p:=(hv' i).smul ((dotL D₀).differentiableAt.comp p he); have hH(j): DifferentiableAt ℝ (H j) p:= (hv' j).smul ((W j).differentiableAt.comp p he);
    have h(j:Axis)(L:Faces→L[ℝ]ℂ) : grad i (fun y:E4=> v j y • L (g y)) p= v j p • L (grad i g p)+grad i (v j) p • L (g p):=by
         change fderiv ℝ (fun y=> v j y • (L ∘g) y) p _= _; rw [fderiv_fun_smul (hv' j) (L.differentiableAt.comp p he)]; change v j p • grad i (L ∘g) p+ _ =_; rw[Maxwell.grad_linear L (hw.live _ hp)]; rfl -- rfl?
    rw[grad, GermD _ ht]; change fderiv ℝ (fun y:E4=>F y+∑ j:Axis,H j y) p _=_; rw [fderiv_fun_add hF (DifferentiableAt.fun_sum (fun j _ => hH j))]; change grad i F p+ grad i (fun y=>∑ j:Axis,H j y) p=_; rw [show grad i F p= _ from h i (R D₀),grad_sum_f _ (fun j _=>hH j),steers i p v χ hv hs,zero_smul,add_zero]; apply congr_arg; refine Finset.sum_congr rfl fun j _=> (h j (W j)).trans (add_comm ..)
noncomputable def twistS(A:TinG)(v:Drive)(g:Spins)(x:E4):Faces:= (∑ i:Axis,v i x • grad i g x)+ (1/4:ℝ) • ∑ i:Axis,∑ j:Axis, grad i (v j) x • cog A i (cog A j (g x))
include hc
lemma cramp(j:Axis): (∑ i:Axis, cog A i (cog A j (grad i g p)))=(2:ℝ) • grad j g p:=by
   have hPay : (∑ i:Axis,G i (G j (grad i g p)))+∑ i:Axis,G j (G i (grad i g p))= _ := show _= (2:ℂ) • grad j g p from (by rw [← Finset.sum_add_distrib]; simp_rw [fun i:Axis=> struck A hc i j (grad i g p)]; simp); rw[← map_sum,show ∑ i:Axis,G i (grad i g p)=0 from hw.lore p hp,map_zero,add_zero] at hPay -- hp shadow
   rw [hPay, two_smul,two_smul]
lemma pays : M p = (-4:ℝ) • R D₀ (twistS A v g p):=by
   unfold vale; rw [auraP p D₀ g v χ hs]; simp only [fun i:Axis=> yarn A i p D₀ hp g v χ hw hv hs];
   let D(i):= v i p • R D₀ (grad i g p); let W:=∑ i:Axis,D i; have he : ∑ i:Axis,∑ j:Axis,v j p • R D₀ (G i (G j (grad i g p)))=(2:ℝ) • W:=by
       rw[Finset.sum_comm]; unfold W; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw[← Finset.smul_sum,← map_sum, cramp A hc p hp g v χ hw hv hs j,map_smul,smul_comm]; -- fill
   simp only[Finset.sum_add_distrib]; rw[he]; unfold twistS; simp_rw [map_add,map_sum,map_smul]; unfold W D; simp_rw [map_sum,map_smul]; module
end YM.Heron
#print axioms YM.Heron.cramp
#print axioms YM.Heron.yarn
#print axioms YM.Heron.pays
