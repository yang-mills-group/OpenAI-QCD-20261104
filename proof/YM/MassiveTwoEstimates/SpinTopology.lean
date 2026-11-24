import YM.MassiveTwoEstimates.SpinAxes
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The topology on the concrete Euclidean spin projection in the massive target. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinTopology
open Massive QCD.Lat Set Matrix
open scoped Matrix.Norms.Frobenius BigOperators

theorem closedCharge {P : Type*} [TopologicalSpace P] :
    IsClosed {p : P × Spikeˣ | KeepsC p.2} := by
  change IsClosed {p : P × Spikeˣ | p.2.val*chargeMatrix*p.2.val.transpose=chargeMatrix}
  apply isClosed_eq _ continuous_const
  fun_prop

private theorem moveCoord (x : E4) (i : Axis) :
    Continuous (fun p : Ortho × Spikeˣ => Ortho.move p.1 x i) := by
  change Continuous (fun p : Ortho × Spikeˣ => ∑ j, p.1.val i j*x j)
  apply continuous_finsetSum
  intro j _
  have h : Continuous (fun q : M4 => q i j) := continuous_apply_apply i j
  have k : Continuous (fun p : Ortho × Spikeˣ => p.1.val) := continuous_subtype_val.comp continuous_fst
  exact (h.comp k).mul_const (x j)

private theorem movedSlash (x : E4) :
    Continuous (fun p : Ortho × Spikeˣ => slash (Ortho.move p.1 x)) := by
  change Continuous (fun p : Ortho × Spikeˣ => ∑ i, ((Ortho.move p.1 x i : ℝ):ℂ) • gamma i)
  exact continuous_finsetSum _ (fun i _ => (Complex.continuous_ofReal.comp (moveCoord x i)).smul continuous_const)

theorem closedEu : IsClosed (euPinSubgroup : Set (Ortho × Spikeˣ)) := by
  change IsClosed ({p : Ortho × Spikeˣ | KeepsC p.2} ∩
    {p | ∀ x, p.2.val*slash x=slash (Ortho.move p.1 x)*p.2.val})
  apply closedCharge.inter
  rw [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_eq
  · fun_prop
  · exact (movedSlash x).mul (Units.continuous_val.comp continuous_snd)

def euProjection : EuPin →* Ortho where
  toFun := EuPin.coord
  map_one' := rfl
  map_mul' _ _ := rfl

theorem euOpen : IsOpenMap EuPin.coord := by
  letI : LocallyCompactSpace M4 := inferInstanceAs (LocallyCompactSpace (Axis → Axis → ℝ))
  letI : SigmaCompactSpace M4 := inferInstanceAs (SigmaCompactSpace (Axis → Axis → ℝ))
  letI : SigmaCompactSpace Spike := inferInstanceAs (SigmaCompactSpace (Pinor → Pinor → ℂ))
  letI : SigmaCompactSpace Spikeᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  have co : IsClosed (unitary M4 : Set M4) := isClosed_unitary
  letI : LocallyCompactSpace Ortho := co.locallyCompactSpace
  letI : SigmaCompactSpace Ortho := co.sigmaCompactSpace
  letI : SigmaCompactSpace Spikeˣ := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
  letI : SigmaCompactSpace EuPin := closedEu.sigmaCompactSpace
  exact euProjection.isOpenMap_of_sigmaCompact SpinReflection.euclidean
    (continuous_fst.comp continuous_subtype_val)

end YM.MassiveTwoEstimates.SpinTopology
#print axioms YM.MassiveTwoEstimates.SpinTopology.closedEu
#print axioms YM.MassiveTwoEstimates.SpinTopology.euOpen
