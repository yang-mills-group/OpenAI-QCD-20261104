import YM.TIPS.Tight
import YM.Elms.Bracken
import YM.Elms.Pacing
import YM.Differ.Ephemeral
/-!
# Package a single support finite-stencil operator into ancestor receipt.
Earn negatives genuinely. This costs the actual horizon projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a θ v A' D C ν Θ Ω α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery -- ?
open Elm Elm.SparK Elm.SparK.Arbor
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)(x:Label d)
local notation "o"=> wrap c b
variable (p: Insertion c 6)(v w z:ℝ)(Pt:BudgetPoint)
-- large but single.PowerP and κ package. omit Economy constants later
open QCD.Creek
variable {F:Density c 6}{q:Bool}{W S K:ℝ}
namespace Tight
variable (h:Tight H A Pt b r F x k l q a s v W S K)
include h
lemma bendsQ (y:ℂ):Tight H A Pt b r (y • F) (y • x) k l q a s v (‖y‖*W) (‖y‖*S) (‖y‖*K):=by
    obtain ⟨P,hv,hp,hq,hX⟩:= h.funded; exact ⟨byG P y,byGP _ hv y,due _ _ _ _ _ P hp y,fun i=> by rw [byArr]; exact hq _, (byWhole _ _ _ _ _ P y).trans (congr_arg (y • ·) hX)⟩
lemma rentsQ (u t:ℝ)(ht:W ≤ u)(hε: K ≤ t): Tight H A Pt b r F x k l q a s v u S t:=by
    obtain ⟨P,hP,hX,h,w⟩:=h.funded; obtain ⟨p,hp,hf,hv⟩:= hX.paid; exact ⟨P, QCD.Acre.Rails.Bank.funds_hi _ hP ht le_rfl,⟨p,hp,hf,hv.trans hε⟩,h,w⟩
end Tight
end YM.Massive.Poised.Plans.Stamp
#print axioms YM.Massive.Poised.Plans.Stamp.Tight.bendsQ
#print axioms YM.Massive.Poised.Plans.Stamp.Tight.rentsQ
