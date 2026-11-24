import YM.Clays.Pane
import YM.Tinus.Nim
import YM.Tinus.WoodR
import YM.Pollen.Budget
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c L:Side}{N B i j k n F:ℕ}{I D:Type}[Fintype I] {A2 T2 Ae At M W0 X:ℝ}{a C t b w x v θ η ξ z m:ℝ}
-- polynomial bound after plan commissioned. Applies deterministic estimates.Support.
namespace Rates
local notation "X" k:arg => ((k:ℝ)+1)
local macro "payments_aes" : tactic => `(tactic| repeat' first | exact Fuel.cons _|exact Fuel.self | apply Fuel.add|apply Fuel.mul|apply Fuel.pow)
local notation "μ0"=> (1/8:ℝ)
local notation "u1"=> (24/256:ℝ)
local notation "α1"=> (25/256:ℝ)
local notation "ε"=> (1/256:ℝ)
open Stags Footprint Push.AbsoluteSums.Reserves Animals
set_option maxHeartbeats 400000 in
lemma polyK (k n F i j:ℕ)(T2 Ae At C θ z:ℝ): Fuel (fun B:ℕ=> gPollen B k n F i j T2 Ae At C θ z):=by
     have h : Fuel (fun B=> hullP B F):=by unfold hullP; payments_aes
     have hb: Fuel (fun B=> Stags.bonus F B (1/256)):=by unfold Stags.bonus Footprint.payment Footprint.degreeIncome Footprint.spread ballCost; push_cast; payments_aes
     have hw: Fuel (fun B=> anth (1/256) (25/256+2*(1/256)) B):=by unfold anth Footprint.payment Footprint.degreeIncome Footprint.spread ballCost; push_cast; payments_aes
     have hc:Fuel (fun B=> mCash B n k F (1/512) (25/256) C):=by unfold mCash mRent beamFee hullP polyPrice; dsimp only; payments_aes
     have hg:Fuel (fun B=>pledgeA B k n F C Ae At T2):=by unfold pledgeA; repeat' first | exact hw | exact hb | exact hc|exact Fuel.cons _| apply Fuel.add | apply Fuel.mul
     have hr:Fuel (fun B=>riseP i j B (1/256) u1):=by unfold riseP; payments_aes
     unfold gPollen; dsimp only; repeat' first|exact h|exact hr|exact hg|exact hb|exact Fuel.cons _|apply Fuel.add|apply Fuel.mul
end Rates
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.Rates.polyK
