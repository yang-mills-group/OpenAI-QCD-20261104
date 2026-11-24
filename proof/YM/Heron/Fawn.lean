import YM.Heron.Cloud
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad)
variable (A:TinG)(hc:TrueC A)(i j k:Axis)(p:E4)(D₀: Faces)(t:ℝ)(ht:0<t)
local notation "B"=> FlipT A
local notation "f°"=>bz A p t D₀
local notation "R"=>dotL
variable {U:Set E4}(hU:IsOpen U) (g f:Spins) (x:E4)(hx:x∈ U)
structure Way(A:TinG)(U:Set E4)(g:Spins):Prop where
   live (x:E4): x∈U → ContDiffAt ℝ ∞ g x
   lore (x:E4): x ∈ U → enD A g x=0
variable (hw:Way A U g)
local notation "G"=> cog A
local notation "J"=> axon p t
include hU hw hx
lemma gore :grad i (enD A g) x=0:=by
    have he: enD A g=ᶠ[𝓝 x] fun _=> 0:=((show ∀ᶠ y in 𝓝 x,y∈U from hU.mem_nhds hx).mono hw.lore); rw [grad,GermD _ he]; simp [D]
include hc
lemma angel : ∑ i:Axis, grad i (grad i g) x=0:=by rw[← tower A hc g (hw.live x hx),enD]; apply Finset.sum_eq_zero; intro i _; rw [gore A i hU g x hx hw,map_zero]
noncomputable def blaze (A:TinG)(f g:Spins)(i j:Axis): E4→ℂ:= streak A f g i j + streak A f g j i
local notation "T"=> blaze A f° g

include ht
lemma flareP : (∑ i:Axis, grad i (T i j) x)= (-(J x)) • R D₀ (grad j g x)+ (grad j J x) • R D₀ (g x)+∑ i:Axis, grad i J x • R D₀ (G i (G j (g x))):=by
    let F:=f°; let hF:= tinge A p D₀ t ht x; let hg:= hw.live x hx
    have he (i j:Axis): grad i (T i j) x=grad i (streak A F g i j) x+grad i (streak A F g j i) x:=by unfold blaze grad D; rw [fderiv_add ((way_a A _ _ _ _ _ hF hg).differentiableAt (by simp)) ((way_a A _ _ _ _ _ hF hg).differentiableAt (by simp))]; rfl
    simp_rw[he,Finset.sum_add_distrib]; rw[Stiff A _, Heron.motion A _, angel A hc hU g x hx hw,hw.lore x hx,gore A j hU g x hx hw,show _= _ from inward A p D₀ t ht x hc, orfe A j p D₀ t ht x hc, longing A p D₀ t ht x hc]; -- F may not rewrite
    · simp only [bore,map_zero,neg_dotProduct,dotProduct_zero,smul_dotProduct,flip_mul, sum_dotProduct,add_zero,zero_add, sub_zero,neg_smul,zero_sub,sub_neg_eq_add, Finset.sum_neg_distrib,neg_neg]
    all_goals first|exact hF|exact hg
omit ht hc hU hw hx
variable (v: Drive)
structure Seam(v:Drive):Prop where
   smooth (i:Axis):ContDiff ℝ ∞ (v i)
   skew (x:E4)(i j:Axis):grad i (v j) x= -grad j (v i) x
variable (hy:Seam v)
noncomputable def brook (A:TinG)(f g:Spins)(v:Drive)(i:Axis)(x:E4):ℂ:= ∑ j:Axis, v j x • blaze A f g i j x
local notation "Ψ"=> blaze A f g
local notation "Σ₁"=> brook A f g v
variable (hf:ContDiffAt ℝ ∞ f x)(hg:ContDiffAt ℝ ∞ g x)
include hf hg hy
lemma bow : ContDiffAt ℝ ∞ (Σ₁ i) x:= ContDiffAt.sum fun j _=> (hy.smooth j).contDiffAt.smul ((way_a A i j f g x hf hg).add (way_a A j i f g x hf hg))
lemma spark : (∑ i:Axis,grad i (brook A f g v i) x)= ∑ j:Axis, v j x • ∑ i:Axis,grad i (blaze A f g i j) x:=by
    have he(i j:Axis): ContDiffAt ℝ ∞ (Ψ i j) x:= (way_a A i j f g x hf hg).add (way_a A j i f g x hf hg)
    let F(i j:Axis):= grad i (v j) x • Ψ i j x; have hd(i): grad i (brook A f g v i) x= ∑ j:Axis,(F i j+ v j x • grad i (Ψ i j) x):=by
         unfold brook; rw [grad_sum_f]; apply Finset.sum_congr rfl; intro j _; unfold grad D; rw[fderiv_fun_smul ((hy.smooth j).differentiable (by simp) x) ((he i j).differentiableAt (by simp))]; exact add_comm ..
         intro j _; exact ((hy.smooth j).contDiffAt (x:=x)).smul (he i j)|>.differentiableAt (by simp)
    simp_rw [hd,Finset.sum_add_distrib]; rw [show (∑ x:Axis, ∑ y:Axis,F x y)=0 from ?_,zero_add,Finset.sum_comm]; simp only[Finset.smul_sum];
    let R':=∑ i:Axis,∑ j:Axis,F i j
    have h:R'= -R':=by
        unfold R'; nth_rw 1 [Finset.sum_comm]; -- might rw both
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; unfold F; rw [hy.skew x j i, neg_smul]; unfold blaze; simp only [Pi.add_apply,add_comm]
    change R'=0; linear_combination (norm:= ring_nf) h/2
omit hf hg
include hc hU hw hx ht
lemma baptism :(∑ i:Axis,grad i (brook A f° g v i) x) = ∑ j:Axis, v j x • ((-(J x)) • R D₀ (grad j g x)+ (grad j J x) • R D₀ (g x)+∑ i:Axis, grad i J x • R D₀ (G i (G j (g x)))) :=by
     rw[spark A g f° x v hy (tinge A p D₀ t ht x) (hw.live x hx)]; simp_rw [fun j:Axis=>flareP A hc j p D₀ t ht hU g x hx hw]
end YM.Heron
#print axioms YM.Heron.baptism
