import YM.Heron.Vossa
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad away open_away)
open Arise.Range
variable (A:TinG)(D₀: Faces)(hc:TrueC A)(p x:E4)(hx:p≠x)(L:List Axis)(i j:Axis)
local notation "B"=> FlipT A
local notation "R"=> cog B
noncomputable def hull(A:TinG)(D₀:Faces):Spins:= -enD (FlipT A) (stocked 0 0 D₀)
local notation "U"=> hull A D₀
noncomputable def pose(A:TinG)(D₀:Faces)(L:List Axis)(p:E4): Spins:=fun y=> deriveL L (hull A D₀) (p-y)
local notation "H"=> pose A D₀
lemma hotH (h:x ≠ 0): ContDiffAt ℝ ∞ U x:= (health A D₀ 0 ((0:ℝ),x) (Ne.symm h)).neg
include hx
lemma nicePose : ContDiffAt ℝ ∞ (H L p) x:= (balla L U _ open_away (fun x h=>hotH A D₀ x h) _ (show p-x∈away from sub_ne_zero.mpr hx)).comp x (f:=fun y:E4=> p-y) (contDiffAt_const.sub contDiffAt_id)
lemma zeroH : H [] p x=bz A p 0 D₀ x:=by
   let Q:=Maxwell.Free.soften 0; let r:ℝ:=‖x-p‖^2
   have hs:= sub_ne_zero.mpr hx; have ht:=sub_ne_zero.mpr (Ne.symm hx); have hf : ContDiffAt ℝ ∞ Q (p-x-0):=liftY 0 ((0:ℝ),p-x) (Ne.symm hs) 0 _ (Ne.symm hs)
   have hg : ContDiffAt ℝ ∞ Q (x-p):= liftY p ((0:ℝ),x) hx 0 _ hx
   have he(i:Axis) : grad i Q (p-x)= -grad i Q (x-p):=by
       have hw: ∀ y:E4,y≠0→(0:ℝ)^2+‖y‖^2≠0:=fun y hh=>by have ht:=norm_pos_iff.mpr hh; positivity
       rw [show grad i Q (p-x)= _ from soften_first (hw _ hs) i, show grad i Q (x-p)= _ from soften_first (hw _ ht) i, norm_sub_rev]; simp only [PiLp.sub_apply]; ring
   unfold Q at he; change -(enD B (stocked 0 0 D₀) (p-x)) = _; simp_rw [bz,enD, fun i:Axis=> bark i 0 D₀ 0 (p-x) hf,sub_zero,fun i:Axis=> he i,neg_smul,map_neg]; -- bark may simp fails
   simp_rw [fun i:Axis=> bark i p D₀ 0 x hg, Finset.sum_neg_distrib,neg_neg]
private lemma grad_budget(h : 0^2+‖x-p‖^2≠ (0:ℝ)):0^2+‖x-p‖^2≠(0:ℝ):=h
lemma loveK : grad i (H L p) x = - H (i::L) p x:=by
    let f:=deriveL L U; let V:E4→E4:=fun y=>p-y; have he : HasFDerivAt V (-(ContinuousLinearMap.id ℝ E4)) x:=by simpa only [zero_sub] using! (hasFDerivAt_const (c:=p) x).sub (hasFDerivAt_id x)
    have ht: DifferentiableAt ℝ f (V x):=(balla L U _ open_away (fun y h=> hotH A D₀ y h) _ (show p-x∈away from sub_ne_zero.mpr hx)).differentiableAt (by simp); change fderiv ℝ (f ∘ V) x _= _; rw [fderiv_comp x ht he.differentiableAt, he.fderiv]; change fderiv ℝ f (V x) (-(basis i))= _; rw[map_neg]; rfl
omit hx
include hc
lemma unbound : Way B away U:=by
   let Q:=stocked 0 0 D₀; refine ⟨fun y hy=> hotH _ _ _ hy,fun y hy=>?_⟩; have ht:(∑ i:Axis,Maxwell.grad i (Maxwell.grad i Maxwell.Green) y)=0:=Maxwell.harmonic hy -- rg
   have hk:Q= roadH D₀ ∘ Maxwell.Green:=by unfold Q; funext y; rw [stocked,soften_zero,sub_zero]; rfl
   have he:ContDiffAt ℝ ∞ Maxwell.Green y:= Maxwell.freeSmooth hy; have hp: (∑ i:Axis,grad i (grad i Q) y)=0:=by
       have hs (i:Axis): grad i Q=ᶠ[𝓝 y] (roadH D₀) ∘ grad i Maxwell.Green:=by filter_upwards [open_away.mem_nhds hy] with x hx; rw[hk]; exact Maxwell.grad_linear _ (Maxwell.freeSmooth hx) _
       simp_rw [show ∀ i:Axis, grad i (grad i Q) y=(roadH D₀) (grad i (grad i Maxwell.Green) y) from fun i=>(GermD (basis i) (hs i)).trans (Maxwell.grad_linear _ (Maxwell.grad_smooth _ he (by simp)) _), ← map_sum,ht,map_zero]
   change ∑ i:Axis,R i (grad i (-enD B Q) y)=0; simp only [grad,D, fderiv_neg]; change (∑ i:Axis,R i (-(grad i (enD B Q) y)))=_; simp_rw [map_neg, Finset.sum_neg_distrib]; rw [show (∑ i:Axis,R i (grad i (enD B Q) y))=0 from (tower B (flips A hc) Q (by rw [hk]; exact (roadH D₀).contDiff.contDiffAt.comp _ he)).trans hp,neg_zero]
lemma mineral {g:Spins}(h:Way B away g): Way B away (deriveL L g):=by
    induction L with
    | nil=>exact h
    | cons a L ih=>
         let F:=deriveL L g; refine ⟨fun y hy=> Maxwell.grad_smooth _ (ih.live _ hy) (by simp),fun y hy=>?_⟩
         have he := gore B a open_away F y hy ih; rw [rose _ _ _ (ih.live _ hy)] at he; unfold enD; refine Eq.trans ?_ he; apply Finset.sum_congr rfl; intro j _; exact congr_arg (cog B j) (Maxwell.grad_comm ((ih.live _ hy).of_le (WithTop.coe_le_coe.mpr le_top)) j a)
lemma care : Way B ({p}ᶜ) (H L p) :=by
     refine ⟨fun x h=>nicePose A D₀ p x (Ne.symm (show x≠p from h)) L, fun x h=>?_⟩; have hp:= Ne.symm (show x≠p from h); let F:= deriveL L U; unfold enD; simp_rw [fun i=> loveK A D₀ p x hp L i, map_neg, Finset.sum_neg_distrib]; change -(enD B F (p-x))=0; rw [(mineral A (hc:=hc) L (unbound A D₀ hc)).lore (p-x) (show p-x≠0 from sub_ne_zero.mpr hp), neg_zero] -- ctor syntax
end YM.Heron
#print axioms YM.Heron.care
#print axioms YM.Heron.zeroH
