import YM.Heron.Cloud
import YM.Heron.Fawn
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad)
variable (A:TinG)(D₀:Faces)(p:E4)(j:Axis)
local notation "B"=> FlipT A
local notation "Z"=> bz A p
variable (z:ℝ×E4)(hz:p≠z.2)
noncomputable def bonk(w:ℝ × E4)(p:E4):ℝ:=(w.1^2+‖w.2-p‖^2)
include hz
lemma liftY(t:ℝ)(y:E4)(h:p≠y):ContDiffAt ℝ ∞ (Maxwell.Free.soften t) (y-p):=by
    have hp: t^2+‖y-p‖^2 ≠ 0:=by have he:= norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h)); positivity
    exact contDiffAt_const.mul ((contDiffAt_const.add (contDiff_norm_sq ℝ).contDiffAt).inv hp)
lemma asPay :bonk z p≠0:=by unfold bonk; have ht:= norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz)); positivity
lemma big : ContinuousAt (fun w=> (bonk w p)⁻¹) z:= (show Continuous fun w=>bonk w p from (by unfold bonk; fun_prop)).continuousAt.inv₀ (asPay _ _ hz)
lemma sine (i:Axis) : ContinuousAt (fun w:ℝ×E4=> grad i (Maxwell.Free.soften w.1) (w.2-p)) z:=by
     refine ContinuousAt.congr (f:=fun w:ℝ×E4 => -2*Maxwell.normal*(w.2-p) i*(bonk w p)⁻¹^2) ?_ ?_
     · exact (continuousAt_const.mul ((Maxwell.compAxis i).continuous.continuousAt.comp (show ContinuousAt (fun w:ℝ×E4=>w.2-p) z from continuousAt_snd.sub continuousAt_const))).mul ((big p z hz).pow _)
     filter_upwards [continuousAt_snd.eventually_ne hz.symm] with w hw; exact (soften_first (asPay p w hw.symm) i).symm
lemma cine(i:Axis): ContinuousAt (fun w:ℝ×E4=> grad j (grad i (Maxwell.Free.soften w.1)) (w.2-p)) z:=by
    let c(i:Axis)(w:ℝ×E4):=(w.2-p) i; have ht(i:Axis): ContinuousAt (c i) z:=(Maxwell.compAxis i).continuous.continuousAt.comp (show ContinuousAt (fun w:ℝ×E4=>w.2-p) z from continuousAt_snd.sub continuousAt_const); let v(w:ℝ×E4):ℝ:=(bonk w p)⁻¹; have hv:= big p z hz
    refine ContinuousAt.congr (f:=fun w:ℝ × E4=> -2 * Maxwell.normal * basis j i * v w^2+8 * Maxwell.normal * c j w*c i w*v w^3) ?_ ?_
    · exact (continuousAt_const.mul (hv.pow 2)).add (((continuousAt_const.mul (ht _)).mul (ht _)).mul (hv.pow _))
    filter_upwards [continuousAt_snd.eventually_ne hz.symm] with w hw; exact (soften_second (asPay p w hw.symm) j i).symm
lemma health : ContDiffAt ℝ ∞ (Z z.1 D₀) z.2:= stance B _ (((liftY p z hz z.1 z.2 hz).comp z.2 (f:=fun y:E4=>y-p) (contDiffAt_id.sub contDiffAt_const)).smul contDiffAt_const)
lemma crisp : ContinuousAt (fun w:ℝ × E4=> Z w.1 D₀ w.2) z:=by
    refine ContinuousAt.congr (f:=fun w:ℝ × E4=>∑ i:Axis, grad i (Maxwell.Free.soften w.1) (w.2-p) • cog B i D₀) (tendsto_finsetSum _ fun i _=> (sine p z hz i).smul continuousAt_const) ?_
    filter_upwards [continuousAt_snd.eventually_ne hz.symm] with w hw; unfold bz enD; simp_rw [fun i:Axis=> bark i p D₀ w.1 w.2 (liftY p z hz w.1 w.2 hw.symm),map_smul]
lemma workGrad :grad j (Z z.1 D₀) z.2 = ∑ i:Axis, grad j (grad i (Maxwell.Free.soften z.1)) (z.2-p) • cog B i D₀:=by
    let f:=Maxwell.Free.soften z.1; let S(i:Axis)(y:E4):= grad i f (y-p); have h:Z z.1 D₀=ᶠ[𝓝 z.2] fun y=> ∑ i:Axis,roadH (cog B i D₀) (S i y):=by filter_upwards [eventually_ne_nhds hz.symm] with y hy; unfold bz enD; simp_rw [fun i:Axis=> bark i p D₀ z.1 y (liftY p z hz z.1 y hy.symm),map_smul]; rfl
    rw [grad,GermD _ h]; unfold D; rw [fderiv_fun_sum];
    · rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro i _; have hp:= Maxwell.grad_smooth i (m:=∞) (liftY p z hz z.1 z.2 hz) (by simp); have he : ContDiffAt ℝ ∞ (S i) z.2:= hp.comp z.2 (f:=fun y:E4=>y-p) (contDiffAt_id.sub contDiffAt_const); exact (Maxwell.grad_linear (roadH (cog B i D₀)) he j).trans (congr_arg _ (show grad j (S i) z.2=_ from shift_gradient hp))
    intro i _; have he: ContDiffAt ℝ ∞ (S i) z.2:=(Maxwell.grad_smooth i (m:=∞) (liftY p z hz z.1 z.2 hz) (by simp)).comp z.2 (f:=fun y:E4=>y-p) (contDiffAt_id.sub contDiffAt_const); exact (roadH _).differentiableAt.comp z.2 (he.differentiableAt (by simp))
lemma afoot : ContinuousAt (fun w:ℝ × E4=>grad j (Z w.1 D₀) w.2) z:=by
    refine ContinuousAt.congr (f:=fun w:ℝ × E4=>∑ i:Axis,grad j (grad i (Maxwell.Free.soften w.1)) (w.2-p) • cog B i D₀) (tendsto_finsetSum _ fun i _=> (cine p j z hz i).smul continuousAt_const) ?_
    filter_upwards [continuousAt_snd.eventually_ne hz.symm] with y hy; exact (workGrad A D₀ p j y hy.symm).symm
end YM.Heron
#print axioms YM.Heron.crisp
#print axioms YM.Heron.afoot
