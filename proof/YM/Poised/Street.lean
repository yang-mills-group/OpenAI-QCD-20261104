import YM.Poised.Links
import YM.Poised.Coats
/-!
## Rotation.Keeps uniform price on finite panels without opening height again
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource
open Lining Lining.Ferry YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Heir AnalyticBridge.SectorAffine.Offset Planned.AtomRegular Push.Uniform
local notation "Ψ₁"=> Faces (Site l)
local notation "F'"=> Lat.Fields c 6
local notation "F₁"=> Lat.Fields l 6
local notation "Y"=> Faces (Site c)
def plaque :ℝ:= Fintype.card Pipes.Shell
lemma plaque_pos :1 ≤ plaque :=Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr ⟨Sum.inl 0⟩)
lemma starline (g:Frame c)(i:Y): ∑ j:Y, ‖signs g i j‖ ≤ plaque:=by
    obtain ⟨⟨v,i⟩,rfl⟩:= (stretch _).surjective i
    rw [← Equiv.sum_comp (stretch (Site c)),Fintype.sum_prod_type (α₁:=Site c), sum_eq_single v]; swap
    · intro b _ hB; apply sum_eq_zero; intro j _; rw [show signs _ _ _=0 from ?_,norm_zero]
      cases i <;> cases j <;> simp only [signs,stretch, Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,Matrix.transpose_apply, Matrix.star_apply] <;> first | (solve| simp [Lat.rotates, Lat.copies, Matrix.blockDiagonal_apply,siteRot, rides,hB,Ne.symm hB]) | rfl
    swap; · simp
    have hx(i j:Modes c 6): ‖Lat.rotates 6 g i j‖ ≤1:= (Cost.north ..).trans (rotation_price (Lat.rotates_law ..))
    refine (Finset.sum_le_sum (g:=fun _=> (1:ℝ)) (fun j _=> ?_)).trans_eq ?_
    · cases i <;> cases j <;> simp only [signs,stretch, Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,Matrix.transpose_apply, Matrix.star_apply] <;> first| exact hx ..| simp | assumption
      apply hx -- simp_norm not assumptions
    simp [plaque]
abbrev mills (g:Lat.Frame c) : Lat.Fields c 6 →L[ℝ] Lat.Fields c 6:= ((slots 6 g).toLinearMap.restrictScalars ℝ).toContinuousLinearMap
def leverL(g:Frame c)(n:ℕ): Lat.Fields c 6 →L[ℝ] Lat.Fields c 6:= (mills g).comp (mantel n)
lemma scepter (g: Lat.Frame c)(n:ℕ): ‖leverL g n‖ ≤ plaque^n:=by
    have ht(A: F'): Creek.load (fun _=>1) A=‖A‖:=by rw [dry _ (fun _=>one_pos)]; simp only [Finset.prod_const_one,one_mul]; exact (norm_def A).symm
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [plaque_pos]); intro i
    let Q:=panel n i; have hp : ‖Q‖ ≤ ‖i‖:=by rw [norm_def,norm_def i]; refine sum_le_sum (fun i _=>?_); unfold Q; rw [angel]; split; exact le_rfl; rw [norm_zero]; positivity
    change ‖changeVars (signs g) Q‖≤_; rw [← ht]; have h : ∀ y:Y,y∈Finset.univ→(∑ i:Y,(1:ℝ)*‖signs g y i‖) ≤plaque*1:=fun y _=>by simpa using starline g y
    apply (lane (signs g) _ _ _ (fun i=>zero_lt_one) (fun i=>zero_lt_one) (zero_le_one.trans plaque_pos) h Q (Brick.regio Q) (chamber ..)).trans; rw [ht]; exact mul_le_mul_of_nonneg_left hp (pow_nonneg (zero_le_one.trans plaque_pos) _)
lemma remark (g:Frame c)(i:Site c)(w:ℝ)(X:F')(ht:X∈ layer Y n)(a:ℕ): leverL g n (framesF (purseX i a w) X) =framesF (purseX i a w) (slots 6 g X):=by
    let f:=purseX i a w; rw [frame_slots c i a w g X]; change slots 6 g (panel n (framesF f X))= _; rw [← frames_panel,past _ _ ht,if_pos rfl]
end Pipes
end YM.Massive.Poised
