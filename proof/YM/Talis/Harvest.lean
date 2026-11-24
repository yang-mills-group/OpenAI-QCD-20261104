import YM.Talis.Graft
import YM.Talis.Void
import YM.Talis.ValueQ
import YM.Lyre.Price
import YM.Talis.Billet
import YM.Talis.Peak
import YM.Differ.Humming
import YM.Bard.Reel
import YM.Magi.Band
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
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
/-!
 # Monetary compounding.E. arbitrary arcs on Plateau. Stamp prices all offsets.
 -/
open Finset Suburb.Melt.Lobby MassiveQCD
open LeaseV FlareV
variable {I:Type}[Fintype I]
local notation "FP" j:arg=> ratioCostV (A.spacing j) (clockQ P₀ A x j)
local notation "qW"=>stipend P₀ A (x:=x) (I:=I)
local notation "U"=>gainV (qW)
variable (b:ℕ)(Jv:IntervalE P₀ A L x z b n) {M:ℕ} (hP:n-b ≤ distV L M z)

-- Arc power gifts.Class.BODY
variable (K:ℝ) (u w a c:ℕ)(hp:1 < L.val)
include hp
lemma fruitsA (hx:w+3<a)(hh:u<a):∀ᶠ x in atTop, Real.exp K ≤ (EV (3+w) x)⁻¹ * measureV L a x * (measureV L u x)⁻¹ ∧ 1 ≤ (EV (3+w) x)⁻¹ * measureV L a x:=by
    let p:=max u (3+w); have hP:p < a:=max_lt hh (by omega)
    have h:PageP L (fun x=>Real.exp K*(EV (3+w) x)* EV u x) p:= ((PageP.budget_lo L (le_max_right ..)).timesL L _).times L (PageP.budget_lo L (le_max_left ..))
    filter_upwards [h.cheaper L hp hP, (buysV L).eventually_ge_atTop 1] with x h hx'; let t:=EV (3+w) x; have hz:0<t:=χone ..; rw [inv_mul_eq_div, ← div_eq_mul_inv]; refine ⟨?_,?_⟩
    · rw [le_div_iff₀ (χone ..),le_div_iff₀ (χone ..),mul_right_comm]; exact h
    rw[le_div_iff₀ (χone ..),one_mul]; exact outR L (3+w) a x hx' (by omega)
lemma fruitsB (hx:w+3<a)(hh:u<a):∀ᶠ x in atTop, Real.exp K ≤ (EV (3+w) x)⁻¹ * (measureV L u x)⁻¹ * measureV L a x :=by
    filter_upwards [fruitsA L K u w a hp hx hh] with x hx using hx.1.trans_eq (mul_right_comm ..)
-- monetary lens-arch header requirement `‖give ...∥ ≤ R₁ in query` = unweighted ref.Rest forecast. derive all basis heights from Startup.T.choose preparing.B.Title PSL
omit hp
lemma ticG (k:ℕ)(s:Finset I) (hp:s.card≤ k)(w y u:I→ℝ)(hU:∀ i,w i*y i*u i= δ)(hD:0≤ δ) : ‖give (w*y*u) s‖=δ^s.card:=by
     rw [choseX δ w y u hU, norm_pow, Complex.norm_real, Real.norm_of_nonneg hD]
lemma groomV (k:ℕ) (t f: I→ℝ)(hv:∀ i,|t i| ≤ K)(he:∀ i,0 ≤ f i ∧ f i ≤1) (hK:1≤K)(s:Finset I)(hs:s.card≤ k): ‖give (t*f) s‖ ≤ K^k:=by
     unfold give; rw[norm_prod]; apply le_trans (b:= K^s.card); · rw[← Finset.prod_const]; refine prod_le_prod (fun i _=> norm_nonneg _) fun i _=>?_ ; rw [Complex.norm_real,Real.norm_eq_abs]; change |t i*f i| ≤K; rw [abs_mul,abs_of_nonneg (he i).1]; exact (mul_le_mul (hv i) (he i).2 (he i).1 (zero_le_one.trans hK)).trans_eq (mul_one _)
     exact pow_le_pow_right₀ hK hs
include hp
lemma pledgeAge (n₁ k v L':ℕ)(ht:k < v)(hv:n₁ +2 < v) :∀ᶠ x in atTop,∀ b≤ τ n₁ x,∀ z≤ b,pitchG L k x b z≤ EV v x:=by
    have h:=PageP.times L (PageP.budget_lo L (le_max_left k (2+n₁))) (PageP.budget_lo L (le_max_right k (2+n₁)))
    filter_upwards [PageP.cheaper L h hp (show max k (2+n₁) < v from by omega)] with x hx b hb z hz
    exact (mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ (uniformV L x 2) (show b-z ≤ τ n₁ x from by omega)).trans_eq (nexE L 2 n₁ x)) (zero_le_one.trans (uniformV ..))).trans hx
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.fruitsA
