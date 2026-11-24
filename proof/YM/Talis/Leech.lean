import YM.Talis.Peak
import YM.Bloom.Shrimp
import YM.Arise.Pence
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
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{hBP:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K hBP)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open Track Depot
namespace Talis
open MintV Suburb.Affair.Nimbus Counter
variable (L:Side)
local notation "EV"=> measureV L
local notation "τ"=>distV L
local notation "Bp"=>run L
open YM.Arise YM.Arise.Bill YM.Arise.Count YM.Bloom YM.Bloom.TreeP
open Vest QCD.Anomaly QCD.Bera QCD.Creek
open QCD.Bloom QCD.Bloom.Buzz YM.Next.Rank.Normal Massive.UV Arise
namespace PageP
variable {T₁:ℝ→ℝ}{v:ℕ}(hv:PageP L T₁ v)
local notation "Hk"=>just L
include hv
lemma tB (b:ℕ):PageP L (fun x=> QCD.Bera.tumbler b (T₁ x)) v:=by unfold tumbler; exact liftNat L (harm L (timesL L hv _) (Hk 1 v)) b
lemma tP (b:ℕ):PageP L (fun x=> QCD.Bera.steely b (T₁ x)) v:=by unfold steely; exact timesL L (tB L hv b) _
lemma dB (b:ℕ):PageP L (fun x=> Anomaly.dime b (T₁ x)) v:=by unfold Anomaly.dime; exact timesL L (liftNat L (harm L (timesL L hv _) (Hk 1 v)) _) _
lemma pB(b:ℕ) :PageP L (fun x=> Anomaly.percent b (T₁ x)) v:=by unfold Anomaly.percent; exact timesL L (dB L hv b) _ -- hv
lemma eB(n m:ℕ):PageP L (fun x=> emmet (T₁ x) (T₁ x) (T₁ x) (T₁ x) n m) v:=times L (times L (liftNat L hv _) (tB L hv _)) (times L (liftNat L hv _) (dB L hv _))
lemma tPB(n:ℕ) : PageP L (fun x=> vibe n (T₁ x) (T₁ x)) v:=harm L (times L (timesL L (liftNat L hv _) _) (tB L hv n)) (times L (liftNat L hv _) (tP L hv n))
lemma shiv(b:ℕ) (c:ℝ):PageP L (fun x=>Anomaly.shiver b (T₁ x) (T₁ x) c c) v:= times L (liftNat L hv _) (harm L (timesL L (dB L hv _) _) (times L (pB L hv b) (Hk _ _)))
lemma trophies(n m:ℕ): PageP L (fun x=> windfall (T₁ x) (T₁ x) (T₁ x) (T₁ x) n m) v:=harm L (times L (tPB L hv _) (times L (liftNat L hv _) (dB L hv _))) (times L (times L (liftNat L hv _) (tB L hv _)) (shiv L hv m _))
lemma peakV' (n m l:ℕ)(t:ℝ):PageP L (fun x=> Arise.Count.splint (T₁ x) t n m l) v:=by unfold Arise.Count.splint Arise.Count.pumpkin; exact liftNat L (times L (times L (eB L hv _ _) (Hk _ _)) (Hk _ _)) _
lemma dawnF (l:ℕ):PageP L (fun x=> MassiveQCD.Play.Chamber.face l (T₁ x)) v := by unfold MassiveQCD.Play.Chamber.face; exact timesL L (liftNat L hv _) _
lemma fBanner (n m l:ℕ)(t:ℝ) : PageP L (fun x=> Arise.Count.corona (T₁ x) t n m l) v:= by unfold Arise.Count.corona; exact times L (liftNat L (harm L (dawnF L (peakV' L hv n m l t) l) (Hk _ _)) l) (times L (trophies L hv _ _) (Hk _ _))
-- card costs
omit hv
section
variable {Z:ℝ→ℕ}(hz:PageP L (fun x=> (Z x:ℝ)) v)
include hz
lemma costsP (a b:ℕ) : PageP L (fun x=> ((a*Z x+b:ℕ):ℝ)) v:=by simp only [Nat.cast_add,Nat.cast_mul]; exact harm L (timesL L hz _) (Hk _ _)
lemma careG (C:Gauge)(d:ℕ): PageP L (fun x=> YM.Bloom.TreeP.fareV C d (Z x)) v:=by unfold YM.Bloom.TreeP.fareV; push_cast; exact times L (liftNat L (harm L (harm L hz hz) (Hk _ _)) _) (Hk _ _)
lemma careS (d:ℕ): PageP L (fun x=> QCD.Bloom.Buzz.audit (Z x) d) v:=by unfold audit; push_cast; exact times L (times L (timesL L (liftNat L (harm L (harm L hz hz) (Hk _ _)) _) _) (Hk _ _)) (Hk _ _) -- parentheses
end
end PageP
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.PageP.fBanner
