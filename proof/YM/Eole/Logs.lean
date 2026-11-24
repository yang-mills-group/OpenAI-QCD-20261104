import YM.Eole.Mint
import YM.Eole.Buds
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
namespace Gain
open QCD.Jets QCD.Jets.Touch QCD Kites Pressure
open ConnectedActivityE6 Reserves Blaze King
open Push.AbsoluteSums.Trees
variable {L0:Side}{v b α:ℝ}
-- enter radius at any chosen fusion level. growth rate o(early meter length) validated later.
variable (L:Side) (k:ℝ→ℕ)
local notation "U"=> highR L
local notation "V"=> taxK L
local notation "ζ"=> fun i:ℝ=>youngF L (k i) i
local notation "Φ"=>perchF L
local notation "S"=>soldE L
local notation "η"=>(1/2:ℝ)
local notation "p₀"=> (28/256:ℝ)
variable (hk:Rate su L 0 fun x=>(k x:ℝ))
include hk
lemma logsV : Rate su L 0 (fun x=>Real.log (youngF L (k x) x)):=by
    let A:=(28/256:ℝ); let v(x:ℝ):ℝ:=↑((k x+k x+1)^4:ℕ); have hh:Rate su L 0 v:=by unfold v; push_cast; exact (((hk.add hk).add (Rate.const _)).pow 4).weaken (by ring_nf; try rfl)
    let w(x:ℝ):ℝ:=fan L (1/3) x; have hw:Rate su L 0 w:= Rate.rpow_monitor _; apply ((hh.mul_left (-A)).add (hw.mul_left (-(1/20:ℝ)))).congr; apply Eventually.of_forall; intro i; change Real.log (youngF L (k i) i)=_ ; unfold youngF taxK; rw[Real.log_mul (Real.exp_pos _).ne' (inv_pos.mpr (Real.exp_pos _)).ne',Real.log_exp,Real.log_inv,Real.log_exp]; dsimp only; rw [neg_mul (1/20)]
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.logsV
