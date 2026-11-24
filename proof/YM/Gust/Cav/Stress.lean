import YM.Euclid.Stress
import YM.Gust.Cav.Words
import YM.Gust.Cav.D
/- Variant of YM.Euclid.Stress, for Spiral register. -/

/-!
# Tensor laws, stress and charge interfaces

E L422-450, at arbitrary center. Fluxes read finite quotients, no
near-diagonal contact term (density differentiates the shell test). This
also supplies centered/angular, or unaveraged versions as needed in bootstrapping
rotation jobs. `O(4)` is the same real matrix convention as raw H on positions;
include generators as HasDerivAt of each orbit (for real evolution parameter).
No conclusion of integration from matrix bracket without the actual action.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spiral
open Function Set Filter MeasureTheory Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {L : Register G} {S : Table L}

namespace Table
abbrev Stress (S : Table L) := Axis → Axis → S.Field 4

structure Conserved (P : DiffPlan S) (H : S.RealSpin) (J : S.Stress) : Prop where
  symmetric : ∀ a b, J a b = J b a
  real : ∀ a b, S.conj H 4 (J a b) = J a b
  divergence : ∀ b, ∑ a : Axis, P.deriv 4 a (J a b) = 0

def RawTensor (H : S.RealSpin) (J : S.Stress) :=
  ∀ k a b, S.mirror H 4 k (J a b) = ∑ i : Axis, ∑ j : Axis,
    (((k.matrix i a * k.matrix j b : ℝ) : ℂ)) • J i j


end Table
end YM.Spiral

#print axioms YM.Spiral.Table.RawTensor
