import YM.VMarker.Plane
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Twist
open Function Lattice Wilson QCD Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Stew Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {J K A B R U I:Type} [Fintype I]
open Stitch Plate
local notation "X"=> Ribbon.Spine I
local notation "Z"=> Keys c N
variable (F: Reel c N I J)(G:Film c N I K)(Y:Rail c N R) (Ω: Grid c→EvenA c N)(V:Grid c)(s:Finset (Ribbon.Spine I))(t:ℝ)
set_option quotPrecheck false
local notation "U★"=> rootR X (Keys c N)
local notation "ξ" w=> relativeE N F G Y w t
lemma wrapUP (P:Grid c→EvenA c N)(p:EvenA c N)(he: Ω V = p+ P V) : (ξ Ω) V = U★ (NormedSpace.exp p)* ((ξ P) V):=by unfold relativeE; rw [he,map_add,add_assoc,exp_add,← map_exp (U★) (U★).toLinearMap.toContinuousLinearMap.continuous,mul_assoc]
lemma freights (A: EvenA c N)(Y:Tine c N I) : pluck Z s (U★ A*Y)=A.val*(pluck Z s Y):=by
   rw [mul_comm (U★ A)]; exact (Apron.Grove.scrape_right ..).trans ((bright A).central (pluck Z _ _)).eq -- ambiguity scrap
lemma pearl_ticket (A : ℝ)(P: Grid c→EvenA c N)(q:Sheet c)(h: Ω V= baker c N A+nozzle c N q+P V): pluck Z s ((ξ Ω) V)= A.exp • (gauss (Lat.copies N q)*pluck Z s ((ξ P) V)):=by
    rw [wrapUP F G Y Ω V t P _ h,freights,exp_add, Coda.tripC, smul_mul_assoc,one_mul]
    rw [show (Real.exp A • NormedSpace.exp _ :EvenA c N).val= Real.exp A • light _ (exp (nozzle c N q)) from map_smul ((Cove.light (Keys c N)).toLinearMap.restrictScalars ℝ) ..,smul_mul_assoc,light_exp, show light _ (nozzle c N q)=_ from QCD.Port.serviceP ..] -- syntax
    rfl
end YM.MassiveQCD.Twist
