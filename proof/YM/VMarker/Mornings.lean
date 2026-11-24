import YM.VMarker.Limbs
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)(Y: Ruby.Hue c N J)(F: Patron.Rail c (ample N I) U)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "b'"=>banknote N p φ
local notation "d!"=> withdraw N p θ
local notation "F!"=> pursue N p θ F φ r
local notation "Y!"=> radial I Y
local notation "K!"=> limb N p θ φ r Y F
namespace Wage
set_option quotPrecheck false
open QCD.Villa QCD.Leaf QCD.Loom QCD.Loom.Fleet QCD.Stew QCD.High QCD.Acre QCD.Meridians QCD.Kites
local notation "bz"=> O.threshold
open QCD.Leaf QCD.Jets
open QCD.Conductor.Tandem
lemma switches (T:BudgetPoint)(h:O.B=T.B)(hx:Switch (N:=N) O L v θ t r w): Switch (N:=N) T L v θ t r w:=by
   constructor
   exacts [hx.count,hx.before,hx.steer,hx.fold,hx.mint,hx.blaze,h ▸ hx.path,h ▸ hx.pool,h ▸ hx.quilt] -- syntax exacts indent
variable {E':Type}
lemma scripts (T:BudgetPoint)(h:O.B=T.B)(ht:O.threshold=T.threshold)(H G:Grid c→EvenA c N)(KZ:QCD.Acre.Rails.Links.Envelope c N)(X:Patron.Rail c N E')(C:ℂ)(hv: Script H G KZ X t v a r O C): Script H G KZ X t v a r T C:=by
    obtain ⟨J,E,Z,hJ,hE,hZ,G0,X',V,hF,hL,hW,hQ,hS,hU'⟩:=hv.spends
    rw [h,ht] at hF hL; rw [h] at hW; rw [ht] at hQ hU'; exact ⟨J,E,Z,hJ,hE,hZ,G0,X',V,hF,hL,hW,hQ,hS,hU'⟩
end Wage
end YM.MassiveQCD.Plate
