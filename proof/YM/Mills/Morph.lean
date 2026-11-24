import YM.Mills.Sorghum
import YM.VMarker.Joust
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.FlareV
open Function Lattice Wilson RG QCD QCD.Lat Kites QCD.Beam
open Pressure MeasureTheory QCD.Loom QCD.Loom.Fleet QCD.Kites QCD.Grass QCD.Acre.Rails Struck Struck.Library
open scoped Topology ContDiff Matrix.Norms.L2Operator BigOperators Classical
open QCD.Jets Cupola Plate SC Ribbon QCD.Cove Stitch
variable {p c:Side}{I J K T D E F:Type} [Fintype I] {N j k:ℕ} (w:I→ℝ) (hv:∀ i,w i≠0)
section
variable (R:Code c N) (S:Reel c N I E)(U:Film c N I F) (A:Grid c→ℝ)(G:Grid c→Sheet c)(P:BudgetPoint)(z:ℂ)
local notation "Φ"=> Bank.pillow R S U A G P z
local notation "Φ₁"=> Bank.pillow R (volume_up S w) (volume_F U w) A G P z
include hv
lemma oneP (s:Finset (Spine I))(V:Grid c): pluck (Keys c N) s (Φ₁ V)= ignites w s • pluck (Keys c N) s (Φ V):=by
    have hh : Φ₁ V = capstone (Keys c N) w (Φ V):=(cashInV S U V _ w P.threshold hv _).symm -- order
    rw [hh,patrol]
end
open QCD.Port Kit YM.Next.Free
variable (F':Reel c N I E)(S:Flight j k)(d:c.val=p.val*S.L.val)(H:KernelChoices)(P Q:BudgetPoint)(F0: Code c N)(Z:Code p N)(X: Film c N I D)(Y:Reel p N I F)(K': Film p N I J)(z v:ℂ)(U:Grid c→ℝ)(T:Grid c→Sheet c)(U':Grid p→ℝ)(T':Grid p→Sheet p)(u β:ℝ)(α:ℂ)(A:Set (Finset I))
include hv
-- homogeneity for *any* view evaluation including noncanonical projections
lemma current (h: Bank.RollL S d H P Q F0 Z F' X Y K' z v U T U' T' u β α A)(s: Finset I)(hs:(s.powerset:Set (Finset I)) ⊆ A)(i:Finset (Ribbon.Spine I))(hi:∀ j∈i,j.1.1∈s) (V:Grid p) :
     let R:= Bank.pillow F0 F' X U T P z; let L:=Bank.pillow Z (volume_up Y w) (volume_F K' w) U' T' Q v
     ignites w i • Kites.engine u (Keys p N) ((S.visit H d).push β (fun U:Grid c=> QCD.Kit.sheath 1 (ater S d U) (pluck (Keys c N) i (R U))) V)=α • pluck (Keys p N) i (L V):=by
    intro R L; rw [h.leg s hs i hi V]; unfold L; rw [oneP w hv Z Y K' U' T' Q v i V, smul_comm]
end YM.MassiveQCD.FlareV
#print axioms YM.MassiveQCD.FlareV.current
