import YM.Elms.Bracken
import YM.Cardinal.Quad
/-! # Tight footprint Volume, additive tools -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a θ v A' D D' C ν Θ Ω α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}{I J K:Type}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {H:TaperHol}{U:Hol su}{A:Exhibit U}{b:Cover}{x y:Label d}{p:BudgetPoint}{q:Bool}
variable (X:CentreFrame (c:=c) p t x q A b (r+1) I Empty)(Y:CentreFrame (c:=c) p t y q A b (r+1) J Empty)
local notation "W'"=>sumup X Y
noncomputable def simple: CentreFrame (c:=c) p t (x+y) q A b (r+1) (I⊕J) Empty:=⟨(sumup X Y).moor, (sumup X Y).p,X.spine⟩
local notation "N"=>simple X Y
variable (hX:Published X H n j a s D 0) (hY:Published Y H n j a s D' 0)
include hX hY
lemma warn : Published (N) H n j a s (D+D') 0:=by
    have h:=sumupP X Y hX D' 0 hY; exact ⟨h.sailX,h.costs,hX.lev,hX.taxed,h.key⟩
lemma ride (V:Grid c)(hp:Pilot H A d m k n j r α β)(hm:p.order=m)(hk:p.power=k)(hP:30*(r+1)≤ c.val)(ht:1 ≤ t)(ha:0 ≤a): Reel.rope (Puff.roll 6 (ritual N)) p.threshold V=Reel.rope (Puff.roll 6 (ritual X)) p.threshold V+Reel.rope (Puff.roll 6 (ritual Y)) p.threshold V:=by
   have ht' (L:Type)(y:Label d)(F:CentreFrame (c:=c) p t y q A b (r+1) L Empty)(u:ℝ)(hF:Published F H n j a s u 0): Summable fun i=> Reel.mist (F.p.roll) p.threshold i V:=by
       obtain ⟨h,hf,hL⟩:=hF.costs; exact grow_shape 6 (wrap c b) _ V ⟨_,fun i=> (hf i).sight,hL⟩ ha ht hF.sailX
   have hF (L:Type)(y:Label d)(F:CentreFrame (c:=c) p t y q A b (r+1) L Empty)(u:ℝ)(hF:Published F H n j a s u 0): Reel.rope (Puff.roll 6 (ritual F)) p.threshold V=vote A b y q F.moor p.threshold (r+1) c V+ Reel.rope (F.p.roll) p.threshold V:=by rw [ritual_eq,rope_plus]; exact congr_arg (fun k=> k+_) (sumBase ..); all_goals first| apply Summable.of_finite| exact ht' L y F u hF
   rw [hF _ _ _ _ (warn X Y hX hY),hF _ _ _ _ hX,hF _ _ _ _ hY,vote_add V X.moor Y.moor] -- hp arguments.probe
   rw [show (Puff.roll 6 ((N).p))=_ from sumupp X Y,rope_plus 6 V _ _ (ht' _ _ _ _ hY) (ht' _ _ _ _ hX)]; abel
omit hX hY
end YM.Massive.Poised.Plans.Stamp
#print axioms YM.Massive.Poised.Plans.Stamp.ride
