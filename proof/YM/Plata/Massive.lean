import YM.Plata.Torch
import YM.Kly.Viceroy

/-!
# Interacting massive QCD in the specified window calibration scheme

Closing the existence statement. Use Wightman/vacuum verification ONLY after
actual same-regulator budgets proved sufficient on **all** characters used for phase selection. See also `project/MassiveSolution.md`.
-/
set_option maxHeartbeats 560000
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Filter Function Mako Tarn Choir Massive.Bridge Massive.Bridge.Kly
open Intag.Sprig Intag.Sprig.Compass
open scoped Topology BigOperators Classical ComplexOrder
/-- The `TheoryAt` in the primary project exists for all sufficiently large
reference inverse couplings, for each positive tolerance.

* `Mako.meru`: path, calibration and continuum system, with mass measurements,
  and key regulator-dependent budget estimates, all in one construction.
* `realization` and `Kly.ascent`: OS Chamber for those moments and the
  character data from the ground algebra.
* Finish those data's use in vacuum selection with `Mako.spar`. Pay the two
  outstanding estimates for the comparison on those same fields. Need Phase
  systems with (for example) the desired PCAC Ward identities still measurable,
  positive metric, and the actual real-spacetime theory conclusion.
-/
theorem interacting_six : YM.Massive.Goal := by
  intro ε he
  filter_upwards [Mako.meru ε he] with β h
  obtain ⟨C, P, K, f, T, hp, hP, -, -, hf, hK, hu, E, X, W, A, I, B, R, ρ, F, w, J, S, hF, N⟩ := h
  obtain ⟨V⟩ := realization N.eu (N.field.reflected timeAxis)
  obtain ⟨B'⟩ := spread_ready V N.eu N.field.increases N.field.exhaustive
  have ht := canto F N V
  obtain ⟨D, hd, -⟩ := Kly.ascent B' ht N.eu (fun p u hu => N.scaling.improper p u hu)
    N.field (fun x => (Gust.eyeP T hK.h timeAxis x).symm)
  apply Mako.spar J hu hK B R S F hF N V B'
  intro p _
  have budget := zeal T ρ A.jet V B' ht N.eu (N.field.reflected timeAxis) D hd p hp hP
    hf.tendsto_atTop hK
  exact ⟨given budget E, tours budget E⟩

end YM.Massive
#print axioms YM.Massive.interacting_six
