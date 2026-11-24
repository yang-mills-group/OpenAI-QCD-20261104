import YM.MassiveTwoEstimates.SpinTopology
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-! Continuous lifts on the whole real parameter line through the actual
two-sheeted Euclidean spin projection, with identity initial lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinPath
open Massive SpinTopology Set
open scoped Topology Matrix.Norms.Frobenius

theorem kernelFinite : (euProjection.ker : Set EuPin).Finite := by
  obtain ⟨q,hq,hqspin⟩ := SpinFibres.euBoth (1:EuPin)
  refine (Set.finite_singleton q).insert (1:EuPin) |>.subset ?_
  intro p hp
  have coord : p.coord=(1:EuPin).coord := hp
  rcases SpinFibres.euFiber p 1 coord with rfl | hminus
  · exact Set.mem_insert _ _
  · have eq : p=q := Subtype.ext (Prod.ext (coord.trans hq) (hminus.trans hqspin.symm))
    exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr eq)

theorem covering : IsCoveringMap EuPin.coord := by
  have cont : Continuous euProjection := continuous_fst.comp continuous_subtype_val
  have quot : Topology.IsQuotientMap euProjection := euOpen.isQuotientMap cont SpinReflection.euclidean
  exact (quot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom kernelFinite.isDiscrete).isCoveringMap

theorem uniqueStart (f : C(ℝ,Ortho)) (h : f 0=1) :
    ∃! g : C(ℝ,EuPin), g 0=1 ∧ EuPin.coord ∘ g=f := by
  apply covering.existsUnique_continuousMap_lifts f (0:ℝ) (1:EuPin)
  exact h.symm

/-- The continuous double cover lifts the full rotation group trajectory
used by the field-covariance statements at all positive and negative times. -/
theorem path (a : Ortho.Skew) : ∃ p, EuPin.Path a p := by
  let f : C(ℝ,Ortho) := ⟨Ortho.oneParameter a, by
    apply Continuous.subtype_mk
    change Continuous (fun t : ℝ => NormedSpace.exp (t • a.val))
    fun_prop⟩
  have at0 : f 0=1 := by apply Subtype.ext; simp [f,Ortho.oneParameter]
  obtain ⟨g,⟨start,lifts⟩,_⟩ := uniqueStart f at0
  exact ⟨g,start,g.continuous,fun t=>congrFun lifts t⟩

end YM.MassiveTwoEstimates.SpinPath
#print axioms YM.MassiveTwoEstimates.SpinPath.covering
#print axioms YM.MassiveTwoEstimates.SpinPath.path
