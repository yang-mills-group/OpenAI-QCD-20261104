import YM.Bard.Track
import YM.Profiles.Counts
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
variable (Z:Borough P₀ gate) (f:Tag P J (fun b=>(P₀ b).guide.table)→ℕ)(pad:ℕ→ℕ→ℕ)(j:ℕ)
local notation "x₁"=> Z.fixed j
local notation "T"=> Z.track f pad
local notation "b"=> Z.starts f pad j
-- observation requests any room & time delays, purchase simultaneous after reference. No uniformity as j varies.
variable (U:ℕ→ℝ→ℕ)(C:ℕ→ℝ→Prop)(hx:∀ j,∀ᶠ s:ℝ in atTop,C j s)
include hx
lemma rehearsalA (s:ℝ)(hV:C 0 (fallback (Z.fixed 0).L s)):∃ pad:ℕ→ℕ→ℕ,∀ j, ∃ i,C j (clockQ P₀ (Z.track f pad) s i) ∧ i≥Z.starts f pad j ∧ (j=0→i=0) ∧ ∀ k:ℕ,k ≤ U j (clockQ P₀ (Z.track f pad) s i)→ Z.Lead f pad j (i+k):=by
   let B(j n:ℕ):=(Z.fixed j).L.val^n
   let r(j d:ℕ):= fallback (Z.fixed j).L (s+su.slopeConstant*Real.log (d:ℝ))
   let R(j d:ℕ):= riseV (Z.fixed j).L (r j d)
   have ht(j):1 < (Z.fixed j).L.val:= lt_of_lt_of_le (by omega :1<3) (Z.fixed j).flight.coarse
   choose c hc using fun j d=> ((aheadV _ (ht j) (r j d)).eventually (hx j)).exists
   let a j d:=if j=0 ∧ d=1 then 0 else c j d
   have ha(j d:ℕ): C j (R j d (a j d)):=by
       unfold a; split; swap; · exact hc j d
       rename_i H; obtain ⟨rfl,rfl⟩:=H; simpa only [R, r,riseV, Nat.cast_one, Nat.cast_zero, Real.log_one, mul_zero, zero_mul,add_zero] using hV
   let pad j n:= (Finset.range (B j n+1)).sup (fun d=> a j d + U j (R j d (a j d)))
   refine ⟨pad,fun j=>?_⟩; let k:= Z.starts f pad j; let A:= Z.track f pad; let X:=(A.den k).val; let v:=a j X
   have hd:X ≤ B j k:= (oldest P₀ A k).trans_eq (congr_arg (fun x:Side=> x.val^k) (spacing_lead P₀ Z f pad j (show Z.Lead f pad j k from ⟨le_rfl,(Z.adj f pad j).1⟩)))
   let C':=U j (R j X v); have hR:v+C' ≤ pad j k:= Finset.le_sup (f:=fun d=> a j d+U j (R j d (a j d))) (Finset.mem_range.mpr (show X < B j k+1 by omega))
   have hU(i:ℕ)(hi:i≤ C') : Z.Lead f pad j (k+v+i) :=by
        refine ⟨show k ≤ k+v+i from by omega, show k+v+i<_ from ?_⟩; unfold Depot.rear; change _<k+Z.Needs f j+pad j k+1; omega
   have hk: clockQ P₀ A s k=r j X:=congr_arg (fun z:Side=>fallback z _) (spacing_lead P₀ Z f pad j (show Z.Lead f pad j k from ⟨le_rfl,(Z.adj f pad j).1⟩))
   have hp: clockQ P₀ A s (k+v) =R j X v:= (risingV P₀ Z f pad j s (by simpa only [Nat.add_zero] using hU 0 (Nat.zero_le _))).trans (congr_arg (fun x=>riseV _ x v) hk)
   refine ⟨k+v,hp.symm ▸ ha j X,Nat.le_add_right ..,(fun hp=>?_ ),fun i hi=> hU i (show i ≤ C' from ?_)⟩
   · subst j; unfold k v a X; dsimp only [k,Depot.starts, Track.den]; norm_num
   change i ≤ U j (clockQ P₀ A s (k+v)) at hi; rw [hp] at hi; exact hi
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.rehearsalA
