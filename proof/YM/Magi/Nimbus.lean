import YM.Bard.Kite
import YM.Hypnos.Rider
import YM.Hypnos.EpochH
import YM.Hypnos.Optic
import YM.VStages.TotemW
import YM.VStages.Votaries
import YM.VStages.Through
import YM.Mills.Pearls
import YM.Rebus.Shocks
import YM.Rebus.Nor
import YM.Rebus.Peep
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
namespace Affair
open Finset Grass NormedSpace MeasureTheory High PrismT
open Lunar Ring0 Stew.Project Sq
set_option quotPrecheck false
variable (B: SparkMesh) (T: Affair P₀ A X B x n)
local notation "q₀"=> clockQ P₀ A x i
local notation "Y₁"=> T.W.state (i+1)
local notation "Y₀"=> T.W.state i
local notation "ϕi"=> stepper P₀ A X B T i
local notation "Lₜ"=> A.spacing i
local notation "cₜ"=> A.ring (B.n k) i
local notation "cᵢ"=> A.ring (B.n k) (i+1)
local notation "Kq"=> K
variable (Pt:ℕ→BudgetPoint)
namespace Nimbus
open MassiveQCD.Rebus Hypnos
open MintV
-- at actual x, launch x1 evaluated from x (at all gates, `run` equals `riseV`). choose ε from heads fixed before.
variable (L: Side)(n i t:ℕ)
noncomputable abbrev cutOffV (A:ℝ) (x:ℝ):ℝ:=run L x ^ (-A)
noncomputable abbrev freshS (n:ℕ)(x:ℝ):ℝ:= cutOffV L (1/2) x * measureV L n x
noncomputable abbrev gemmaV (x:ℝ):ℝ:= 2* run L x ^ (1/2:ℝ)
lemma slideV (x:ℝ):run L x= riseV L x 1:=by unfold run riseV; simp [betaF]
lemma frost (n:ℕ):Rate su L (-(1/2)) (freshS L n):=by convert Rate.mul (Rate.power (a:=-(1/2:ℝ)) (G:=su) (L:=L)) (rateMeasure L n) using 1; ring
lemma magV' : Rate su L (1/2) (gemmaV L):=Rate.mul_left Rate.power 2 -- order
local notation "EV"=>measureV L
local notation "Bᵥ"=>run L
lemma rainingV (hL:1<L.val):∀ᶠ x in atTop,fiery su x L ≤ freshS L 3 x :=by
    filter_upwards [curtailV L 2 1 hL,Delay.shift_pos su L] with x hx hz
    have hr:=hx 0 (Nat.zero_le _); have hv:riseV L x 0=x:=by simp [riseV]
    rw [hv] at hr
    have hi:0≤ Bᵥ x:= hz.le; unfold fiery Pressure.temp; rw [Real.sqrt_eq_rpow]; unfold freshS cutOffV; rw [Real.rpow_neg hi]; apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.rpow_nonneg hi _)); exact (Real.rpow_one _).symm.le.trans hr
lemma escapeF (a b:ℕ)(hL:1<L.val)(hp:3≤a)(ht:a<b) : ∀ᶠ x in atTop,EV 1 x * (fiery su x L + freshS L a x) ≤ freshS L b x:=by
   filter_upwards [goCost L a b 2 2 hL ht,rainingV L hL,(buysV L).eventually_ge_atTop 1,Delay.shift_pos su L] with x hx h h₁ hz
   let v:= cutOffV L (1/2) x; have hP:0≤ v:=Real.rpow_nonneg hz.le _
   calc _ ≤ EV 1 x*(2 * (v * EV a x)):=mul_le_mul_of_nonneg_left (by linarith only [show fiery su x L ≤ v* EV a x from h.trans (mul_le_mul_of_nonneg_left (outR L 3 a x h₁ hp) hP)]) (zero_le_one.trans (uniformV ..))
        _ ≤ EV a x*(2 * (v*EV a x)):=mul_le_mul_of_nonneg_right (outR L 1 a x h₁ (by omega)) (by have ht:0≤EV a x:= zero_le_one.trans (uniformV ..); positivity)
        _= v*(2*EV a x^2):=by ring
        _ ≤ _:= mul_le_mul_of_nonneg_left hx hP
lemma chantingV (C D:ℝ)(a b:ℕ)(hp:a<b)(hC:1≤C)(hD:1≤D)(hL:1<L.val):∀ᶠ x in atTop, C*chant (freshS L a x) (gemmaV L x) D+1≤ EV b x:=by
    filter_upwards [frost L a |>.below (by norm_num) 1 zero_lt_one,Delay.shift_pos su L,goCost L a b 1 (4*D*C+1) hL hp] with x h hz hu
    rw [pow_one] at hu; let p:= freshS L a x; have hp1: EV a x ≥ 1:=uniformV ..; have hp:0 ≤ p:= mul_nonneg (Real.rpow_nonneg hz.le _) (zero_le_one.trans hp1)
    let u:= Bᵥ x^(1/2:ℝ); have hH: gemmaV L x*p=2*EV a x:=by unfold p freshS cutOffV gemmaV; rw [Real.rpow_neg hz.le]; field_simp
    have he:p^2 ≤ p:= by nlinarith only [hp,show p≤1 from (le_abs_self _).trans h]
    unfold chant
    calc
        _≤ C*(gemmaV L x*(D*p+D*p)) + 1:=by gcongr
        _=4*D*C*EV a x+1:=by linear_combination 2*C*D*hH
        _≤ _:=by nlinarith only [hp1,hu]
lemma marchingV (K:ℝ):∀ᶠ x in atTop,∀ β β':ℝ, Bᵥ x /2 ≤ β → β ≤2*Bᵥ x →0≤ β' →β' ≤ 2*Bᵥ x → |β-β'| ≤K → |(gStep β)⁻¹|≤ gemmaV L x ∧ |(gStep β')⁻¹|≤gemmaV L x ∧ |(gStep β)⁻¹-(gStep β')⁻¹| ≤ K:=by
    filter_upwards [(Work.E09.betaF_growth su L).eventually_ge_atTop 4] with x hx β β' hf hv hn hh hz
    have hs:(Bᵥ x)≥4:=hx; have h0:0≤β:=by linarith
    have hZ (v':ℝ)(hp:0≤v')(he:v' ≤ 2*Bᵥ x): Real.sqrt v' ≤gemmaV L x:=by unfold gemmaV; rw [←Real.sqrt_eq_rpow]; nlinarith [Real.sq_sqrt hp,Real.sq_sqrt (by linarith:0 ≤ Bᵥ x),Real.sqrt_nonneg (Bᵥ x)]
    have ht(v:ℝ):(gStep v)⁻¹=Real.sqrt v:=inv_inv (Real.sqrt v)
    rw [ht β,ht β',abs_of_nonneg (Real.sqrt_nonneg β),abs_of_nonneg (Real.sqrt_nonneg β')]
    have he : 1 ≤Real.sqrt β+Real.sqrt β':=by nlinarith [Real.sqrt_nonneg β,Real.sq_sqrt h0,Real.sqrt_nonneg β']
    refine ⟨hZ β h0 hv,hZ β' hn hh,?_⟩
    apply le_trans _ hz
    have ht:|Real.sqrt β-Real.sqrt β'| *|Real.sqrt β+ Real.sqrt β'|= |β-β'|:=by rw [←abs_mul]; congr 1; nlinarith [Real.sq_sqrt hn,Real.sq_sqrt h0]
    rw [←ht]; exact le_mul_of_one_le_right (abs_nonneg _) (he.trans (le_abs_self _))
end Nimbus
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.Nimbus.escapeF
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.Nimbus.chantingV
