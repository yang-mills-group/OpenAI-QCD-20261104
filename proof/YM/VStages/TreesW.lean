import YM.VStages.Municipal
import YM.Massive.Spire.Rebase
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
variable {R:Rock j}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (Y:Metros P J θ F₀ χ)(T:TrackQ (gate:=gate) Y)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
lemma augmented (i x): run (T.spacing i) (clockQ Y T x i)= T.scale x i:= fall ..
lemma engaged (x:ℝ)(i:ℕ): T.scale x (i+1)=run (T.spacing i) (T.scale x i):=T.eras x i
abbrev seat (i:ℕ):Side:= T.spacing (i-1)
abbrev clockK (x:ℝ)(i:ℕ) := fallback (seat Y T i) (T.scale x i)
lemma notch (i:ℕ): seat Y T (i+1) = T.spacing i:=by unfold seat; rw[Nat.add_sub_cancel]
lemma terminal (i:ℕ)(x:ℝ): run (T.spacing i) (clockQ Y T x i)= run (seat Y T i) (clockK Y T x i):=by rw [clockK,augmented,Spire.Client.fall]
lemma start_clock (i:ℕ)(x:ℝ): clockK Y T x (i+1)= run (T.spacing i) (clockQ Y T x i):=by rw [augmented,clockK,notch,engaged Y T]; unfold Spire.Client.fallback run betaF; ring -- order check
lemma radSecond (d ν:ℝ)(L:Side)(x:ℝ) : ν*roofK L θ d x=d*roofK L θ ν x:=by unfold roofK Emax; ring
-- currency seat w lo price. change f-demand now. choose gate for threshold.
local notation "Pz"=> seat Y T i
local notation "Lz"=> T.spacing i
abbrev valueK (i:ℕ):ℝ:= (Y (T.node i)).κ
abbrev MassBox (x:ℝ)(i:ℕ):= roofK (seat Y T i) θ (valueK Y T (i-1)) (clockK Y T x i)
-- Force slack: permit (L/128-1). gate relative bound via lo next possibilities; handles i=0, self manual.
structure Growth (gate:ChangeQ→ℕ) :Prop where
   nextQ :∀ b c, b.hi=c.lo→∀ r:ℕ, gate c ≤ r →3*(Y b).κ ≤ ((r:ℝ)/128-1)*(Y c).κ
   selfQ :∀ b (r:ℕ), gate b ≤ r → 3*(Y b).κ ≤ ((r:ℝ)/128-1)*(Y b).κ
lemma Growth.rise (v:Growth Y gate) (f:ChangeQ→ℕ)(hf:gate≤f):Growth Y f:= ⟨fun b c h r hr=> v.nextQ b c h r ((hf c).trans hr),fun b r hr=> v.selfQ b r ((hf b).trans hr)⟩
lemma reproduction (f:ChangeQ→ℕ):∃ gate:ChangeQ→ℕ,f≤gate ∧ Growth Y gate:=by
   let M(b):= max (Y (steady b.lo)).κ (max (Y (enter (b.lo-1))).κ (Y b).κ)
   have h(c:ChangeQ):Tendsto (fun x:ℕ=>((x:ℝ)/128-1)*(Y c).κ) atTop atTop:= (tendsto_atTop_add_const_right _ (-1) (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num:(0:ℝ)<128))).atTop_mul_const (Y c).pos
   choose k hk using fun b=> eventually_atTop.1 ((h b).eventually_ge_atTop (3*M b))
   refine ⟨fun b=>max (k b) (f b),fun b=>le_max_right ..,⟨?_,fun b r hr=> (mul_le_mul_of_nonneg_left ((le_max_right _ (Y b).κ).trans (le_max_right _ _)) (by norm_num)).trans (hk b _ ((le_max_left ..).trans hr))⟩⟩
   intro b c hf r hr; apply le_trans _ (hk c r ((le_max_left ..).trans hr)); apply mul_le_mul_of_nonneg_left _ (by norm_num); unfold M
   obtain ⟨i,j,h⟩:=b; rcases h with h|h
   · subst j; rw [←hf]; exact le_max_left ..
   subst j; rw [← hf]; exact (le_max_left (Y (enter i)).κ _).trans (le_max_right _ (max (Y (enter i)).κ _)) -- defeq
lemma ceilingW (h:Growth Y gate) (hp:0≤MassBox Y T x i): MassBox Y T x i ≤ ((↑(T.spacing i).val:ℝ)/128-1)*roofK (T.spacing i) θ (valueK Y T i) (clockQ Y T x i):=by
   let L:= T.spacing i; let H:=seat Y T i; let d:=valueK Y T (i-1); let s:=valueK Y T i; let q:= MassBox Y T x i; let r:=roofK L θ s (clockQ Y T x i); have hs:0<s:=(Y _).pos; have hd:0< d:= (Y _).pos; let a:= (L.val:ℝ)/128-1
   have ht:3*d ≤ a*s:=by
        change 3*valueK Y T (i-1) ≤((↑(T.spacing i).val:ℝ)/128-1)* (valueK Y T i); cases i with
        | zero=> exact h.selfQ _ _ (T.sizing _)
        | succ j=> rw [Nat.add_sub_cancel]; exact h.nextQ (T.node j) (T.node (j+1)) rfl _ (T.sizing _)
   have he: r*L.val*d=q*H.val*s:=by
        unfold q r MassBox; change roofK L θ s _ * _ * d=roofK H θ d _ * _ * s
        rw [Spire.radMaximum (terminal Y T i x)] -- L is let
        have H':= radSecond (θ:=θ) d s H (clockK Y T x i); change _=_* (↑H.val:ℝ) *s ;
        convert congr_arg (fun x:ℝ=>x*(H.val:ℝ)) H'.symm using 1 <;> ring
   have hv: L.val ≤ 3*H.val:=by
       change (T.spacing i).val ≤ 3*(seat Y T i).val
       cases i with
       | zero=> unfold seat; rw [Nat.zero_sub]; omega
       | succ i=> rw [notch]; simp_rw [Track.spacing,T.length_eq]; exact (T.nexts i).2.2.2
   have hL:(L.val:ℝ) ≤ 3*(H.val:ℝ):=by exact_mod_cast hv
   change q ≤ a*r
   apply le_of_mul_le_mul_right (a:=(L.val:ℝ)*d) _ (by positivity)
   calc q*(L.val*d) ≤ q*(3*(H.val:ℝ)*d):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL hd.le) hp
        _= q*H.val*(3*d):=by ring
        _ ≤ q*H.val*(a*s):=mul_le_mul_of_nonneg_left ht (mul_nonneg hp (by positivity))
        _= a*(q*H.val*s):=by ring
        _ = a*r*(L.val*d):=by rw [← he]; ring
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.reproduction
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.ceilingW
