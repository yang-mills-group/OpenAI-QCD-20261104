import YM.Differ.Humming
import YM.Oars.Mother
import YM.Affina.Rem
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
open MassiveQCD.Sample Sail
open Rails.Bank.Hike
set_option quotPrecheck false
variable (L:Side)
local notation "W" x:arg=> (highR L x+1:ℕ)
local notation "Q" x:arg=> (↑(highR L x+1:ℕ):ℝ)
local notation "n1" x:arg=>riseV L x (W x)
local notation "B" x:arg=>highR L (n1 x)
local notation "v" x:arg=> fan L θ (n1 x)
variable (Wχ:ℕ→ℝ)(U S:ℝ)
-- long exponential bill
local notation "Lr"=> Real.log (L.val:ℝ)
local notation "X★" x:arg => ((L.val:ℝ)^(W x))^4
variable (ℓ:ℝ→ℕ)
open Counter.Hymn
local notation "E" x:arg => Real.exp (-(pitchD 8*((highR L x:ℝ)*Lr -(ℓ x:ℝ)*Lr)))
local notation "Z" x:arg=> roomAt L θ (riseV L x (ℓ x))
variable (hn:1< L.val)(bn:ℕ) (hWz:∀ᶠ x in atTop,ℓ x ≤ distV L bn x)
include hn hWz
lemma clocksB (a:ℝ): Rate su L a (fun x=> X★ x * E x):=by
     let p:= Lr; have hp:0<p:=Real.log_pos (by exact_mod_cast hn)
     refine ((Hearth.paysA a (ε:= p/8) (by positivity) L).mul_right (Real.exp (4*p))).compare ?_
     filter_upwards [smallerV L bn (1/100) (by norm_num),hWz] with x hx hk; have hWz₁:(ℓ x:ℝ) ≤ _:= (Nat.cast_le.mpr hk).trans hx
     have hz:X★ x=Real.exp ((Q x)*4*Lr):=by
         rw [show Q x*4*Lr=Real.log (X★ x) from by rw[Real.log_pow,Real.log_pow]; push_cast; ring,Real.exp_log (by positivity)]
     rw [abs_of_nonneg (by positivity : 0 ≤ X★ x * E x),abs_of_nonneg (by positivity),hz]
     rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr; push_cast; change (_+1)*4*p+ -(pitchD 8*(_*p-(ℓ x:ℝ)*p)) ≤ -(p/8)*_+_;
     unfold pitchD; norm_num; nlinarith! only [mul_le_mul_of_nonneg_right hWz₁ hp.le,mul_nonneg (Nat.cast_nonneg (highR L x)) hp.le]
variable (F G:ℝ→ℝ)
lemma billedH (KV:ℝ)(bk:ℕ)(hM:Rate su L a G)(hv:Rate su L η (fun x=>(F x)⁻¹))(hf:∀ᶠ x in atTop,0<F x ∧0<G x) :∀ᶠ x in atTop, 0<(measureV L bk x)⁻¹ *(Z x/(E x*G x)) ∧ X★ x* Real.exp KV ≤ F x *((measureV L bk x)⁻¹ *(Z x/(E x*G x))):=by
      have hh:∀ᶠ x in atTop,ℓ x ≤ W x:= by
             filter_upwards [smallerV L bn 1 zero_lt_one,hWz] with x hx hp; apply (hp.trans ?_).trans (Nat.le_succ (highR L x)); rw [one_mul] at hx; exact_mod_cast hx
      have hz: Rate su L 1 (fun x=> (Z x)⁻¹):= roseR L (inverseSlot L θ) ℓ hh
      have hw:= ((((((clocksB L ℓ hn bn hWz (-2-a-η)).mul (rateMeasure L bk)).mul hM).mul hz).mul hv).mul_right (Real.exp KV))
      have hX:= (aheadΩ L _ (shuttle L θ))
      filter_upwards [hf,hw.below (by linarith) 1 zero_lt_one,hX] with x hx hk hp; let m:= measureV L bk x; let C:= E x; let X':= X★ x; have hM:0 < m:=zero_lt_one.trans_le (uniformV ..); have hC:0 < C:= Real.exp_pos _; have hu:=mul_pos hC hx.2; let p:=Z x; have hP:0 < p:=(hp _).1; have hv:0 < m⁻¹ * (p/(C*G x)):=mul_pos (inv_pos.mpr hM) (div_pos hP hu); refine ⟨hv,?_⟩
      apply (_root_.div_le_one (mul_pos hx.1 hv)).mp; have hE: X' *C*m* G x * p⁻¹ * (F x)⁻¹ * Real.exp KV ≤1:= (le_abs_self _).trans hk; change X'* Real.exp KV/(F x*(m⁻¹ *(p/(C*G x))))≤ _; rw [show X'* Real.exp KV/(F x*(m⁻¹ *(p/(C*G x))))= X'*C*m*G x*p⁻¹*(F x)⁻¹*Real.exp KV from by field_simp]; exact hE
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.billedH
