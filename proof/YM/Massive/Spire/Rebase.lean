import YM.Massive.Spire.Overlook
import YM.QCD.Cabin.Bend
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
namespace Stratum.Spire
open Rails
/-!
# Exact currencies shared by the two flights through a level

Write every regular metadata on the *station* whose next coarser
stride pays it. `i=0` in the thermal scale convention is the only station
with no coarser step. This doesn't identify pressure windows or projection maps
from flight to flight, only the calculable budgets listed below.
-/
variable {T:Side}{s t y:ℝ}
section prices
variable (he: run L x=run T y)
include he
lemma goNow (h: Now L P G x): Now T P G y:= ⟨h.era, h.baseG.trans (congr_arg temp he), h.ball.trans (congr_arg radiusB he)⟩
lemma curtain : haloK L x = haloK T y := congr_arg (fun x:ℝ=>x^(-(1/32):ℝ)) he
lemma fine : pra L x=pra T y:=by unfold pra Delay.fineMonitor; rw [show betaF su x L=_ from he]
lemma pitch_at (θ:ℝ):fan L θ x=fan T θ y:=congr_arg (fun x:ℝ=>x^θ) (fine he)
lemma chip_at : Jets.Touch.chip L x=Jets.Touch.chip T y:=by unfold Jets.Touch.chip; rw [fine he,show betaF su x L=_ from he]
lemma flash (p:ℝ): taxK L x p=taxK T y p:=by unfold taxK; rw [pitch_at he]
lemma radMaximum (θ ν:ℝ): roofK L θ ν x * L.val= roofK T θ ν y*T.val:=by unfold roofK Emax speedP; rw [chip_at he,pitch_at he,div_mul_cancel₀ _ (side_pos T).ne',div_mul_cancel₀ _ (side_pos L).ne']
lemma verge [Countable I][Countable J'] (Q:Cove.Rise f N I J')(u:I→ℝ)(v:J'→ℝ)(h:TraceR Q P L t s x u v): TraceR Q P T t s y u v:=by
   obtain ⟨h₁,h₂,h,a⟩:= h
   rw [pitch_at he] at h₁
   have hf: highR L x = highR T y := congr_arg radiusB he
   rw [flash he, chip_at he,hf] at h₂
   exact ⟨h₁,h₂,h,a⟩
lemma germSet (b':Flavor N)(A:Voice f N)(h: Enn P b' L x t s (duo A.P A.K)): Enn P b' T y t s (duo A.P A.K):=by
   obtain ⟨x,z,h,hp⟩:= h; rw [pitch_at he] at hp; exact ⟨x,z,verge he _ _ _ h,hp⟩
end prices

open Fog.Mist YM.Massive.Stratum
variable {cB:ℝ} {α β N₁ y:ℝ} {θ:ℝ} {c f C L:Side}
namespace Client
variable {R:Rock j}{F₀:Flavor N}{χ:Chi} (P₀: Client j R N F₀ χ)
local notation "Gₚ"=> passportM j P₀.good
variable (A:AtlasH R (passportM j P₀.good) P₀.guide.table) (X:∀ i, SlotH P₀ θ A i)
open AtlasH
abbrev seat (i:ℕ):Side:= A.length (i-1)
abbrev clockC (x:ℝ)(i:ℕ) := fallback (seat P₀ A i) (A.scale x i)
lemma input_seat (i:ℕ): seat P₀ A (i+1) = A.length i:=by unfold seat; rw[Nat.add_sub_cancel]
lemma terminal (i:ℕ)(x:ℝ): run (A.length i) (precursor P₀ A x i)= run (seat P₀ A i) (clockC P₀ A x i):=by rw [clockC,season,fall]
lemma start_clock (i:ℕ)(x:ℝ): clockC P₀ A x (i+1)= run (A.length i) (precursor P₀ A x i):=by rw [season,clockC,input_seat,← second P₀ A]; unfold fallback run betaF; ring -- order check
local notation "Pz"=> seat P₀ A i
local notation "Lz"=> A.length i
abbrev MassBox (x:ℝ)(i:ℕ):= roofK (seat P₀ A i) P₀.θ P₀.κ (clockC P₀ A x i)
lemma seat_cap (hp: 0 ≤ MassBox P₀ A x i): MassBox P₀ A x i ≤ 3 * roofK Lz P₀.θ P₀.κ (precursor P₀ A x i):=by
   let γ:= MassBox P₀ A x i; let δ:= roofK Lz P₀.θ P₀.κ (precursor P₀ A x i); have he:δ*(Lz).val=γ*(seat P₀ A i).val:=radMaximum (terminal P₀ A i x) P₀.θ P₀.κ -- parentheses
   let ν:ℝ:=(A.length i).val; let b:ℝ:= (seat P₀ A i).val
   have h:ν ≤3*b:= by
       unfold ν b; have h:(A.length i).val≤3*(seat P₀ A i).val:=by
           cases i with
           | zero=> unfold seat; rw [Nat.zero_sub]; omega
           | succ i=> rw [input_seat]; exact A.gradual _
       exact_mod_cast h
   have hb :0<b:= side_pos _; have ht:0<ν:=side_pos _
   change γ ≤ 3*δ; apply le_of_mul_le_mul_right (a:=ν) _ ht; change δ * ν=γ * b at he; nlinarith only [he,mul_le_mul_of_nonneg_left h hp]
end Client
end Stratum.Spire
end YM.QCD.Acre
