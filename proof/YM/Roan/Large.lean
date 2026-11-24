import YM.Roan.EditP
import YM.Tinus.WoodR
import YM.Tinus.Nim
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
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
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
namespace MintV
open Finset Real
open MassiveQCD.Sample YM.Intag YM.Intag.Receipt Basal Sail
open Rails.Bank.Hike
set_option quotPrecheck false
variable (L:Side)
local notation "Y₁" x:arg=> fan L θ x
local notation "Y₂" x:arg=> fiery su x L
local notation "tt" x:arg=> run L x
-- Develop inverse ratios only because scale λ uses reverse. speedy diff from log
local notation "W" x:arg=> (highR L x+1:ℕ)
lemma treaties (M:ℕ):∀ᶠ z in atTop,let e:=1/(↑(W z):ℝ)^M; ∀ j,j ≤ W z → let y:= riseV L z j; |(Y₁ y)/(Y₁ (tt y))-1|≤e ∧ |(Y₂ y)/(Y₂ (tt y))-1|≤e :=by
      let U:= fun z=> (↑(W z):ℝ)^M; have ht:= ((Rate.power (G:=su) (L:=L) (a:= (-(1/2):ℝ))).mul ( (opusR L).pow M)).below (by norm_num) 1 zero_lt_one
      obtain ⟨h,h₁⟩:= welcomeQ (θ:=θ) L; filter_upwards [ht,busR L h (-(1/2)) (by norm_num),busR L h₁ (-(1/2)) (by norm_num)] with x hx hp hh; have he:0 < U x:=pow_pos (show 0 < (↑(W x):ℝ) from by push_cast; positivity) _; have h : (tt x)^(-(1/2:ℝ)) ≤1/U x:= (le_div_iff₀ he).mpr ((le_abs_self _).trans hx); exact fun i hi=> ⟨(hp i hi).trans h,(hh i hi).trans h⟩
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.treaties
