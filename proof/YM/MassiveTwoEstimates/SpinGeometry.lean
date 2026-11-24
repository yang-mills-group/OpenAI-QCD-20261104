import YM.MassiveTwoEstimates.SpinParity
import YM.MassiveTwoEstimates.LorentzTopology
import YM.MassiveTwoEstimates.SpinLorentz

/-! The complete Euclidean and Lorentzian spin geometry required by the
massive QCD target, independently of the dynamical field estimates. -/
namespace YM.MassiveTwoEstimates.SpinGeometry
open Massive

theorem geometry : Geometry :=
  ⟨SpinReflection.euclidean, SpinLorentz.realTime, SpinTopology.euOpen,
    LorentzTopology.realOpenOfSurjective SpinLorentz.realTime, SpinFibres.euBoth,
    SpinFibres.minkBoth, SpinFibres.euFiber, SpinFibres.minkFiber, SpinReflection.unitary,
    SpinAxes.reflection, SpinPath.path, BoostMotion.boost, SpinParity.full, SpinAxes.spatial⟩

end YM.MassiveTwoEstimates.SpinGeometry
#print axioms YM.MassiveTwoEstimates.SpinGeometry.geometry
