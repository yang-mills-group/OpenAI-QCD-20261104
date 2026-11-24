import YM.MassiveTwoEstimates.BoostMotion
import YM.MassiveTwoEstimates.BoostRoom

/-! Every element of the target proper orthochronous group is covered by
its concrete charge-preserving Lorentzian spin matrices. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinLorentz
open Massive Mink

theorem realTime : Function.Surjective RealSpin.coord := by
  intro g
  obtain ⟨e,r,K,hK,eq⟩ := BoostRoom.decompose g
  obtain ⟨p,hp⟩ := SpinReflection.euclidean K
  have spatial : Lorentz.spatialTurn p.coord := hp ▸ hK
  obtain ⟨q,hq,_⟩ := SpinAxes.spatial p spatial
  refine ⟨BoostMotion.point e r*q,?_⟩
  change e.boost r*q.coord=g
  rw [eq,hq]
  congr 1
  apply Lorentz.ext
  intro x
  change Ortho.move p.coord x=Ortho.move K x
  rw [hp]

end YM.MassiveTwoEstimates.SpinLorentz
#print axioms YM.MassiveTwoEstimates.SpinLorentz.realTime
