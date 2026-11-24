import YM.TorusPCAC.Spec.History
import YM.RG.Push
import YM.Push.BETA_TRANSPORT.Block
import YM.QCD.Cedar.Canopy
import YM.QCD.Step.Gallery

/-!
# No further measure normalization assumptions inside a step
(Produce the `NormalizedStep` condition over our actual patch convention.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Finite
open QCD QCD.Lat Lattice Wilson RG MeasureTheory Function Filter Finset QCD.Flume
open scoped Topology BigOperators Matrix.Norms.Frobenius Matrix ComplexOrder
variable {c f : Side} {N : ℕ} (J : StepData c f)
open Grass

lemma mean_usable : Continuous (meanSpin (N:=N) J) := (Kit.choir_cont N).comp (QCD.Pine.tied_cont ..)

lemma high_cont (X : Density f N) (h : Continuous X) : Continuous (TorusPCAC.high J X) := by
  let G : Matrix (Modes c N) (Modes f N) ℂ × Fields f N → Fields c N := fun z => Kit.sheath 1 z.1 z.2
  change Continuous (G ∘ fun i : Grid f => (meanSpin J i,X i))
  exact (show Continuous G from (Kit.sheath_cont (b:=1))).comp ((mean_usable (N:=N) J).prodMk h)

variable (H : J.patch.Branches J.kernel su)
include H
lemma continuous_block (X : Density f N) (h : Continuous X) (b w : ℝ) : Continuous (TorusPCAC.block J b w X) := by
  have hp : Integrable (TorusPCAC.high J X) (prior su f) :=
    (high_cont J X h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
  have he : Continuous (J.push b (TorusPCAC.high J X)) := by
    rw [continuous_iff_continuousAt]; intro x; rw [← continuousWithinAt_univ]
    exact (Push.BetaTransport.push_continuousWithinAt (X:=Fields c N) J H (b:=fun _=>b) (y:=x)
      continuousWithinAt_const (V:=id) continuousWithinAt_id (F:=fun _=>TorusPCAC.high J X) hp
      (Eventually.of_forall fun _=> hp.1) (ae_of_all _ fun _=> continuousWithinAt_const)
      hp.norm (Eventually.of_forall fun _=> ae_of_all _ fun _=> le_rfl)).2
  exact (rescaleSpin (c:=c) (N:=N) w).toLinearMap.continuous_of_finiteDimensional.comp he

omit H in
lemma rescale_amp (q : ℝ) (x : Fields c N) :
    ber _ (rescaleSpin q x)=(q:ℂ)^(2*Fintype.card (Modes c N))*ber _ x := by
  rw [rescaleSpin, Grass.volume_map]; simp_rw [Matrix.det_smul, Matrix.det_one, mul_one,two_mul,pow_add]

/-- Works also on a product insertion, on any external coefficient carried
through as an input density, and prior to proving any nonzero fermionic
partition. The actual equality on **total volume** in the paper. -/
theorem normalized (b w : ℝ) (N : ℕ) : NormalizedStep J b w N := by
  have hK:= J.isKernel H b
  refine ⟨hK,fun X h=>?_⟩
  have hp : Integrable (TorusPCAC.high J X) (prior su f) :=
    (high_cont J X h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
  refine ⟨fun V=> StepData.push_slice hK V _ hp,continuous_block J H X h ..,?_⟩
  unfold Density.volume TorusPCAC.block
  simp_rw [rescale_amp, integral_const_mul]; congr 1
  let W : Fields c N →L[ℂ] ℂ:=LinearMap.toContinuousLinearMap (ber _)
  change (∫ U, W (J.push b (TorusPCAC.high J X) U) ∂prior su _)= _
  rw [W.integral_comp_comm (StepData.push_integrable hK _ hp),StepData.push_integral hK _ hp,← W.integral_comp_comm hp]
  congr 1; funext x; exact Kit.insulate one_ne_zero ..

omit H in
lemma vol_grade {A : Type*}[Fintype A](x : Dirac A) : ber A (grade x)=ber A x := by
  conv_lhs => rw [← Grass.both x]
  simp only [map_add,show grade (Grass.plus x)=_ from plus_grade x,
    show grade (minus x)= -minus x from minus_grade x,map_neg]
  conv_rhs => rw [← Grass.both x]
  rw [map_add, odd_loss (minus_grade x)]; simp

omit H in
lemma marginal_grade {A B : Type*}[Fintype A][Fintype B](x : Dirac (A⊕B)) :
    grade (marginal A B x)=marginal A B (grade x) := by
  apply (perfect B).injective; apply LinearMap.ext; intro y
  have he : ∃ u, y=grade u:=⟨grade y,(grade_twice y).symm⟩
  obtain ⟨y,rfl⟩:=he; have hh : grade (far A B y)=far A B (grade y):=pass_grade ..
  rw [perfect_apply,← map_mul,vol_grade,marginal_test,perfect_apply,marginal_test,← hh,← map_mul,vol_grade]

omit H in
lemma high_grade (X : Density f N) (U) : grade ((TorusPCAC.high J X) U) =
    (TorusPCAC.high J (fun V=> grade (X V))) U := by
  let v:=gauss (Kit.joinD 1 (meanSpin J (N:=N) U) 0); have hh:= show grade v=v from gauss_plus _
  unfold TorusPCAC.high Kit.sheath; rw [map_smul,marginal_grade,map_mul,hh,near,pass_grade]

theorem block_grade (X : Density f N) (h : Continuous X) (b w : ℝ) :
    TorusPCAC.block J b w (fun V=>grade (X V))=fun V=>grade (TorusPCAC.block J b w X V) := by
  funext i; unfold TorusPCAC.block
  rw [show grade (rescaleSpin w (J.push b (TorusPCAC.high J X) i)) = rescaleSpin w (grade (J.push b (TorusPCAC.high J X) i)) from Grass.exterior_parity ..]
  congr 1
  let W := (LinearMap.toContinuousLinearMap (grade (A:= Pairs (Modes c N))).toLinearMap).restrictScalars ℝ
  have he := (normalized J H b w N).2 X h
  rw [show grade (J.push b (TorusPCAC.high J X) i) = ∫ U, W (J.density b U i • (TorusPCAC.high J X) U) ∂prior su _ from
    (W.integral_comp_comm (he.1 i)).symm]
  unfold StepData.push; congr 1; funext x; rw [map_smul]; exact congrArg (J.density b x i • ·) (high_grade J X x).symm

lemma block_add (b w : ℝ) (X Y : Density f N) (h : Continuous X) (ht : Continuous Y) :
    TorusPCAC.block J b w (X+Y) = TorusPCAC.block J b w X + TorusPCAC.block J b w Y := by
  have he (X : Density f N) (hx : Continuous X) : Integrable (TorusPCAC.high J X) (prior su f):=
    (high_cont _ X hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
  funext i
  simp only [TorusPCAC.block,Pi.add_apply]
  rw [show TorusPCAC.high J (X+Y) = TorusPCAC.high J X + TorusPCAC.high J Y by
    ext1 x; simp only [TorusPCAC.high,Kit.sheath,Pi.add_apply,map_add,add_mul,smul_add],
    StepData.push_add (J.isKernel H b) _ _ (he X h) (he Y ht), Pi.add_apply,map_add]

omit H in
theorem block_smul (a : ℂ) (b w : ℝ) (X : Density f N) :
    TorusPCAC.block J b w (a • X)= a • TorusPCAC.block J b w X := by
  funext i; unfold TorusPCAC.block StepData.push TorusPCAC.high Kit.sheath; simp only [Pi.smul_apply,map_smul,smul_mul_assoc]; simp_rw [smul_comm _ a,integral_smul,map_smul]
end YM.TorusPCAC.Finite
#print axioms YM.TorusPCAC.Finite.normalized
