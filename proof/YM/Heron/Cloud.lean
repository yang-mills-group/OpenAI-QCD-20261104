import YM.Heron.Step
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
variable (A:TinG)(i j k:Axis)(p:E4)(D₀: Faces) (t:ℝ)(ht:0<t)
local notation "B" => FlipT A
local notation "R" => cog B
noncomputable def stocked (p:E4)(t:ℝ)(D₀: Faces)(x:E4): Faces:= soften t (x-p) • D₀ -- arg order
noncomputable def bz (T:TinG)(p:E4)(t:ℝ)(D₀:Faces):Spins:= enD (FlipT T) (stocked p t D₀)
noncomputable def axon(p:E4)(t:ℝ)(x:E4):ℝ:= source t (x-p)
open Maxwell (grad)
variable (x:E4)
local notation "fz"=> bz A p t D₀
local notation "F"=> stocked p t D₀
local notation "K"=> axon p t
include ht
lemma rife : ContDiffAt ℝ ∞ F x:= (((soften_diff ht).of_le (m:=∞) le_top).contDiffAt.comp x (f:=fun y:E4=>y-p) (contDiffAt_id.sub contDiffAt_const)).smul contDiffAt_const
lemma tinge : ContDiffAt ℝ ∞ fz x := stance B F (rife p D₀ t ht x)
lemma torso : ContDiffAt ℝ ∞ K x := ((source_diff ht).of_le (m:=∞) le_top).contDiffAt.comp x (f:=fun y:E4=>y-p) (contDiffAt_id.sub contDiffAt_const)
omit ht
noncomputable def roadH(D₀: Faces): ℝ →L[ℝ] Faces:= (ContinuousLinearMap.id ℝ ℝ).smulRight D₀
lemma fareC (r:ℝ):roadH D₀ r=r • D₀:=rfl
lemma bark(h: ContDiffAt ℝ ∞ (soften t) (x-p)) : grad i F x=grad i (soften t) (x-p) • D₀:=by
    change grad i (roadH D₀ ∘ (fun y:E4=> soften t (y-p))) _=_; rw [Maxwell.grad_linear _ (show ContDiffAt ℝ ∞ (fun y:E4=>soften t (y-p)) x from h.comp x (f:=fun y:E4=>y-p) (contDiffAt_id.sub contDiffAt_const)), shift_gradient h]; rfl
include ht
lemma goad : grad i (grad i F) x = grad i (grad i (soften t)) (x-p) • D₀:=by
   rw [show grad i F=roadH D₀ ∘ fun x:E4=>grad i (soften t) (x-p) from funext fun y=> bark _ _ _ _ _ ((soften_diff ht).contDiffAt.of_le le_top)]; have h:ContDiffAt ℝ ∞ (grad i (soften t)) (x-p):=Maxwell.grad_smooth _ ((soften_diff ht).contDiffAt) le_top; rw [Maxwell.grad_linear _ (show ContDiffAt ℝ ∞ (fun y:E4=> grad i (soften t) (y-p)) x from h.comp x (f:=fun y:E4=>y-p) (contDiffAt_id.sub contDiffAt_const)), shift_gradient h]; rfl
variable (hc:TrueC A)
include hc
lemma inward : enD (FlipT A) fz x = (-axon p t x) • D₀:=by
   unfold bz; rw [tower B (flips A hc) F (rife p D₀ t ht x)]; simp_rw[goad _ _ _ _ ht, ← Finset.sum_smul]; exact congr_arg (· • D₀) (congr_fun (minus_lap ht) (x-p)) -- explicit hc
lemma orfe : grad i (enD B fz) x = -(grad i K x) • D₀:=by
    have he := inward A p D₀ t ht; rw [show (enD B fz)= roadH D₀ ∘ (-K) from funext fun y=> he y hc, Maxwell.grad_linear _ (show ContDiffAt ℝ ∞ (-K) x from (torso p t ht x).neg), Maxwell.grad,D,fderiv_neg]; rfl
lemma longing : ∑ i:Axis,grad i (grad i fz) x= ∑ i:Axis, (-(grad i K x)) • cog B i D₀:=by
   rw [← tower B (flips A hc) fz (tinge A p D₀ t ht x)]
   change (∑ i:Axis, R i _) = _; simp_rw [orfe A _ p D₀ t ht x hc,map_smul] -- need only outer fold
end YM.Heron
#print axioms YM.Heron.orfe
