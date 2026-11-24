import YM.Cardinal.Quad
import YM.VStages.RideW
import YM.VMarker.Epoch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j kP k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j kP}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open MeasureTheory
lemma movedQ (F: Grid f→ Lat.Fields f n)(V: Grid c) : Massive.transfer S K h a w F V = Kites.engine w (Cove.Keys c n) ((S.visit K h).push a (fun U=>Kit.sheath 1 (ater S h U) (F U)) V):= rfl
lemma moveV (F:Pixel f n)(V:Grid c) : Massive.transfer S K h a w (Cove.light (Cove.Keys f n) ∘ F) V= Kites.engine w (Cove.Keys c n) (advanceF S K h F a V):= rfl
lemma scalar_transfer (F:Grid f→Fields f n) (k:ℂ): Massive.transfer S K h a w (k • F) = k • Massive.transfer S K h a w F:=by
    funext V; rw [movedQ]; change _= k • Massive.transfer S K h a w F V; rw [movedQ, ← map_smul]; apply congr_arg; unfold StepData.push; rw [← integral_smul k]; refine integral_congr_ae (ae_of_all _ (fun U=>?_)); change _ • Kit.sheath _ _ (k • _) = _; rw [Bank.priceTY]; exact smul_comm ..
namespace Bank
open MassiveQCD.Plate QCD.Kites Massive.Poised.Plans.Stamp
variable {Ua:YM.Source.Hol su}{V₁:YM.Massive.Lining.Temper.Collage.Exhibit Ua}{Θ:Massive.SourceRead.TaperHol}{M₁ M₂ t:ℝ}{Z0:Massive.UV.Label n}{A0:Cover}{q':Bool}
lemma funds_hi (Y:CentreFrame (c:=f) P t Z0 q' V₁ A0 (k+1) I J')(h:Published Y Θ i l a u M₁ M₂) (he:M₁≤ d)(hr:M₂≤z): Published Y Θ i l a u d z:=by
   refine ⟨h.sailX,?_,h.lev,?_,h.key⟩
   · obtain ⟨f,hb,hP⟩:= h.costs; exact ⟨f,hb,fun i=>budget_loosen (hP i) he⟩
   obtain ⟨b,hb,hP⟩:= h.taxed.price; exact ⟨b,hb,fun i=>budget_loosen (hP i) hr⟩
end Bank
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.scalar_transfer
