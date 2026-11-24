import YM.Patria.Brute
import YM.TorusPCAC.Geometry.Bare
/-! Transport signed, flavor, charge and translation on Cylinder full fields. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {i j k d N n:ℕ}{c f r:Side}
open QCD.Revolve
open TorusPCAC.Geometry TorusPCAC.Finite TorusPCAC.Ward
open Next.Free
abbrev march (b:Cover)(X:Density c 6):Density c 6:= TorusPCAC.Geometry.post 1 1 (wrap c b) (heat b) X
namespace Exposure
variable (M: StepData c f)(X: Density f 6)(Y: Density c 6)(s:Signed)(p: EuPin)(U: Grid c)(R:Regulator c 6)
variable (hp:p.Lifts s)
local notation "ψ" => M.ratio
local notation "W" => TorusPCAC.high M
local notation "κ" => TorusPCAC.block
variable (hc:M.patch.Branches M.kernel su)(v w:ℝ)(hX: Continuous X)(b:Cover)
include hp in
lemma pin_pivot (hr:R.t=0) : Action.pin p s R.density=R.density:= by rw [pinned,torusDensity]; apply bare_pivot (EuPin.retains s hp) _ _; change Glare s R.t R.t _ _; rw [hr]; exact smoke ..
lemma move_pivot (hr:R.t=0): march b R.density=R.density:=by rw [torusDensity]; apply bare_pivot QCD.Revolve.Swing.none _ _; change Glare _ R.t R.t _ _; rw [hr]; exact TorusPCAC.Geometry.glares _
include hp hc hX in
lemma pin_travel : Action.pin p s (κ M v w X)= κ M v w (Action.pin p s X):= by
   rw [pinned,pinned]; have h:(M.ratio).embed 0=0:= map_zero M.ratio.root; have hh:= post_block (EuPin.retains s hp) M hc v w (show Glare s _ _ (M.ratio.embed 0) (prism s) from (by rw [h]; exact smoke s)) X hX -- cast rew zero all? 
   rw [h,show prism s ∘ M.ratio.embed = prism s from funext (fun x=>step_prism s M.ratio x)] at hh; exact hh
include hc hX in
lemma move_travel : march b (κ M v w X) = κ M v w (march (M.ratio.count.val • b) X):=by
    have h:= Ratio.embed_wrap M.ratio b; let B:= M.ratio.count.val • b; have hh:= post_block QCD.Revolve.Swing.none M hc v w (show Glare 1 0 (0:Site f) (M.ratio.embed (wrap c b)) (heat B) from (by rw [h]; exact glares _)) X hX; rw [h,show heat B ∘ M.ratio.embed=heat b from funext fun i=> heat_child M.ratio b i] at hh; exact hh
-- flavor Circle
variable (u:FlavorTorus)
abbrev proclaim(u:FlavorTorus): TorusPCAC.Ward.Grade 6:= fun i=> ⟨(u i).val, by
    have he : star (u i).val * (u i).val=1:= (u i).property.1
    have h:= congr_arg (fun x:ℂ=>‖x‖) he; rw [norm_mul,norm_star,norm_one] at h; change (u i).val ∈ Metric.sphere 0 1; rw [mem_sphere_zero_iff_norm]; nlinarith [norm_nonneg (u i).val]⟩
-- Proof fill
lemma flavor_show : Action.flavor u Y=fun U=> acts (proclaim u) c (Y U):=by
    funext U; unfold Action.flavor Action.flavorF TorusPCAC.Ward.acts Kit.disguise TorusPCAC.Ward.tag
    apply congrFun (congrArg DFunLike.coe ?_) (Y U) -- or directly
    congr 1
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,Matrix.diagonal_transpose]; rfl
lemma flavor_pivot : Action.flavor u R.density= R.density:= by rw [flavor_show,torusDensity]; exact funext fun _=>tag_formula ..
include hc hX in
lemma flavor_shift : Action.flavor u (κ M v w X)=κ M v w (Action.flavor u X):= by
    funext U; simp_rw [flavor_show]; let g:= TorusPCAC.high M X; let h:= Kit.disguise (TorusPCAC.Ward.tag c (proclaim u)); let L:= h.toLinearMap; change acts _ _ (temp _ ((M.push v g) U))= _
    rw [← temp_acts]; rw [show acts (proclaim u) c ((M.push v g) U)= _ from (congr_fun (Pass.evaluate M v hc L g ((high_cont M X hX).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..))) U).symm]
    have hh : (fun U'=> L (g U'))=TorusPCAC.high M (fun V=>acts (proclaim u) f (X V)):= funext fun i=> high_acts ..; rw [hh]; rfl
open TorusPCAC.Geometry.AxisB
lemma stillB (Q: Spike): Action.moved 1 Q (n:=c) (F:=6) = Jobs c 6 Q:=by
    have he : star (star Q)=Q:=star_star _; nth_rw 1 [← he]; rw [← rotor]; unfold hues Jobs onSpin; rw [he]; congr 1; ext i j; simp [rides,rr,shiftE,Signed.actEquiv,prism,Lining.Ferry.sheet_pace] -- inspect
lemma charge_west : Action.charge Y= fun U=> TorusPCAC.Stencil.charge c (Y (TorusPCAC.Stencil.conjGrid U)):=by
   funext U; unfold Action.charge TorusPCAC.Stencil.charge; rw [shifted]; unfold Switch.shiftC; congr 2
   rw [stillB,stillB,transpJob]; unfold Jobs copies; rw [opposite]; congr 2; ext i j; simp [← neg_ite,Matrix.blockDiagonal_apply]; split <;> first| rfl| simp
lemma charge_pivot : Action.charge R.density=R.density := by rw [charge_west,torusDensity]; exact funext fun i=> compass ..
include hc hX in
lemma charge_shift : Action.charge (κ M v w X)= κ M v w (Action.charge X):= by
   let T:= TorusPCAC.Stencil.conjGrid (n:=c); let V:= TorusPCAC.Stencil.conjGrid (n:=f); let G:= TorusPCAC.Stencil.charge c (N:=6)
   funext U; rw [charge_west,charge_west]; let f'(U':Grid f):= M.density v U' (T U) • (W X U'); have hf0:Continuous (W X):= high_cont M X hX; have hf : Integrable f' (prior su f):=StepData.push_slice (M.isKernel hc ..) (T U) _ (hf0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)); have hk : MeasurePreserving V (prior su f) (prior su f):= Reflection.grid_preserve
   have hx : AEStronglyMeasurable f' (Measure.map V (prior su f)):= hk.map_eq.symm ▸ hf.aestronglyMeasurable; have hV:Continuous V:= Reflection.grid_cts; let HW:= W X ∘ V
   have ht : M.push v (W X) (T U)=M.push v HW U:=by
       change (∫ U,f' U ∂prior su f)=_; rw [show (∫ U',f' U' ∂prior su f) =∫ U',f' (V U') ∂prior su f from (by rw [← integral_map hk.aemeasurable hx,hk.map_eq])]; apply integral_congr_ae; exact .of_forall fun x=> congr_arg (· • HW x) (Reflection.noise M x hc v U) -- smul infer ℝ
   change TorusPCAC.Stencil.charge c (temp (w:ℂ) _)= temp _ _; have hs(t : Fields c 6) : TorusPCAC.Stencil.charge c (temp (w:ℂ) t)=temp (w:ℂ) (G t):=by unfold G TorusPCAC.Stencil.charge; rw [shifted,shifted]; exact Switch.moved ..
   rw [hs]; change temp (w:ℂ) (G (M.push v (W X) (T U))) =_
   rw [ht, show G (M.push v HW U) = _ from (congr_fun (Pass.evaluate M v hc G.toLinearMap _ ((hf0.comp hV).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..))) U).symm]; rw [show (fun x=>G.toLinearMap (HW x))= W (fun U=>TorusPCAC.Stencil.charge f (X (V U))) from funext fun _=>step_charge ..]
end Exposure
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Exposure.charge_shift
#print axioms YM.Massive.Patria.Exposure.flavor_show
