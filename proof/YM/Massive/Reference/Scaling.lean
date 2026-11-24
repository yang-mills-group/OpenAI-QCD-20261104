import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Shoot
import YM.Massive.Pressure.Minor
import YM.Massive.Pressure.Smoothed
import YM.Massive.Tuner.Flat
import YM.Massive.Tuner.Empty
import YM.Massive.Stiffness.Limit
import YM.Massive.Tuner.Common
import YM.Massive.Reference.Schedule
import YM.Massive.Pressure.Major
import YM.QCD.Tide.Palace
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N)
namespace Reference
open Next.Rank IV
variable {s t A'' :ℝ}
open NormedSpace
open MeasureTheory
open YM.SectorNext.Vacuum (rich spare)
open YM.Massive.Pressure (scent_one)


/-!
# Send a cutoff/reference tower on fixed-stride path into an actual Run in the prescribed scheme

Along with all growing-step density/mass estimates on this SAME run before and after blocking.
Existence component, not the desired passage to progressive strides for exact slopes and field
budgets.
-/

open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open YM.Massive.Reading (planeProbe)


variable {K1 K2 θc : ℝ} {L1:HaarBudget su}

variable (hG: Regular L1 θc K1 K2 T' Q B b' x κ τ' g P' X Y D W' k V U Wv A0)

lemma ratioSpacing (hw:O.Branches K su) (m : ℕ) : ((fixed O K hw).spacing m) = ((O.L.val : ℝ)^m)⁻¹:=by unfold Massive.Scheme.spacing; rw [ratio,PNat.pow_coe,Nat.cast_pow]
lemma ratioLog (hw : O.Branches K su) (m:ℕ) : Real.log (((fixed O K hw).spacing m)⁻¹)=m*Real.log O.L.val:=by rw [ratioSpacing,_root_.inv_inv,Real.log_pow]
include hG
lemma increment (i m:ℕ) (hi:i+m≤n) : |V i - (V (i+m) - Raft.Tally i m Y)|≤2*m:=by
  induction m with
  | zero => simp [Raft.Tally]
  | succ m ih=>
     have h := hG.vocals (i+m) (by omega); obtain ⟨hp,he⟩:=abs_le.mp h.2.2.1
     obtain ⟨ht,hV⟩:= abs_le.mp (ih (by omega))
     apply abs_le.mpr; unfold Raft.Tally at *; rw [sum_range_succ] at *; rw [← Nat.add_assoc]; push_cast; constructor <;> linarith
lemma toll (hw:O.Branches T'.bind su)(m:ℕ)(hm:m≤ n): |(fly B hw V U Wv n k N).β m - run O.L x - m*(Raft.betaQ N*Real.log O.L.val)| ≤ m*(D+2)+N*W':=by
   let a:= n-m; have ht: a+m=n:=Nat.sub_add_cancel hm; have hh:=hG.finish.1; change |V a-_-_| ≤_
   obtain ⟨hx,hb⟩:= abs_le.mp (hG.receipts a m ht.le)
   obtain ⟨hc,hp⟩:= abs_le.mp (increment B b' _ A0 hG a m ht.le); rw [ht,hh] at hc hp; apply abs_le.mpr; constructor <;> linarith only [hx,hb,hc,hp]
omit hG

-- one fixed accuracy ε on the slope (to avoid arbitrary-precision confusion)
variable (O : Patch)
lemma lifetime (hw:O.Branches K su)(hp: 2 ≤ O.L.val) : Tendsto (fixed O K hw|>.spacing) atTop (𝓝[>] 0):=by
   rw [tendsto_nhdsWithin_iff]; have hx : 1 < (O.L.val : ℝ):= by exact_mod_cast (show 1<O.L.val from hp)
   refine ⟨?_ ,Eventually.of_forall (fun i => ?_)⟩; swap; · rw [ratioSpacing]; change 0 < ((O.L.val:ℝ)^_)⁻¹; positivity
   simp_rw [funext (ratioSpacing hw)]; exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hx)

lemma within (hw:O.Branches K su) (hp:2 ≤ O.L.val)(hx:0< ε)(hA:D+2 ≤ ε/2*Real.log O.L.val):∀ᶠ m:ℕ in atTop, ∀ β:ℝ, |β-run O.L x - m*(betaQ N* Real.log O.L.val)| ≤ m*(D+2)+N*W' → |β / Real.log (((fixed O K hw).spacing m)⁻¹)-betaQ N| ≤ ε:=by -- remove implicit U
    let r:= run O.L x; let a:=Real.log O.L.val; let t:= ε/2*a; have ha:0<a:= Real.log_pos (by exact_mod_cast (show 1 < O.L.val from hp)); have ht:0<t:=by unfold t; positivity
    filter_upwards [eventually_gt_atTop (0:ℕ), (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop ((|r|+N*W')/t)] with m hm hV β h
    rw [ratioLog]; obtain ⟨h1,h2⟩:= abs_le.mp h; have ht':|r|+N*W' ≤ (m:ℝ)*t:= (div_le_iff₀ ht).mp hV; have hc : 0 < (m:ℝ)*a:=by positivity
    change |β / ((m:ℝ)*a)-betaQ N| ≤ _
    apply abs_le.mpr; unfold t at *; constructor
    · rw [le_sub_iff_add_le]; apply (le_div_iff₀ hc).mpr; unfold r a at *; linarith only [neg_le_abs (run O.L x),ht',mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg (α:=ℝ) m), h1]
    rw [sub_le_iff_le_add]; apply (div_le_iff₀ hc).mpr; unfold r a at *; linarith only [le_abs_self (run O.L x),ht',mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg (α:=ℝ) m), h2]
lemma SIX : Massive.betaSlope= betaQ 6 ∧ 0 < Massive.betaSlope:=by
    have he:Massive.betaSlope= betaQ 6:= by unfold Massive.betaSlope betaQ Pearl.chargeF; push_cast; ring
    rw [he]; exact ⟨rfl,(ultraviolet _).2 (by decide)⟩
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.within
