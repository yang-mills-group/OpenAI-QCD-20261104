import YM.Roan.Port
import YM.Oars.Mother
import YM.Roan.Asia
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
local notation "W" x:arg=> (highR L x+1:ℕ)
local notation "Q" x:arg=> (↑(highR L x+1:ℕ):ℝ)
local notation "n1" x:arg=>riseV L x (W x)
local notation "B" x:arg=>highR L (n1 x)
local notation "v" x:arg=> fan L θ (n1 x)
variable (Wχ:ℕ→ℝ)(U S:ℝ)
local notation "Gw" x:arg=> Wχ (B x)* (v x)^2
local notation "y" x:arg=> riseV L x (highR L x)
local notation "nX" x:arg=> n1 x
local notation "A!" x:arg =>roomAt L θ (riseV L x (highR L x))
local notation "T!" x:arg =>roomAt L θ (n1 x)
local notation "u!" x:arg=> fiery su (n1 x) L
local notation "v!" x:arg=> v x
local notation "wQ" x:arg=> (v! x)^2
open Basal Basal.Rates
open Surge
variable (nF kF pF nL kL iF:ℕ)(vT At M₀ a' b':ℝ) (hΩ:0≤M₀)(ht₀:0≤vT)(he₀:0≤At)(ha:0 ≤ a')(hb:0≤ b')
local notation "tK" x:arg => (expense (κ:=b') (a:=a') nF kF pF nL kL iF vT At M₀ S (B x))
local notation "μ0"=> (1/8:ℝ)
local notation "b₂" => (25/256:ℝ)
local notation "τ"=> (1/512:ℝ)
local notation "b₁"=>(24/256:ℝ)
local notation "b₀"=>(1/8:ℝ)
local notation "ε"=>(1/256:ℝ)
local notation "Sp" bQ:arg=> Basal.riseP nL kL bQ ε b₁
local notation "Fp" bQ:arg=> MassiveQCD.Plate.Stags.bonus nF bQ ε
local notation "V★" bQ:arg=> Surge.trekV nF kF pF iF At M₀ vT 0 bQ
local notation "cM"=> M₀ +6*(M₀+M₀)
variable (hS0:1 ≤ S)(he:0< θ) (g:ℝ)(hg:0 ≤ g)
-- h(H)=Pho extends.M.Ph grants unit.For all COST spur.W; canonial M.
local notation "P!" x:arg H:arg => (A! x/H)
include hS0 he ht₀ he₀ ha hb hΩ
-- startup wallets.One_H. 
include hg
lemma grantCap :∀ᶠ x in atTop, let U0:=u! x; let v0:= v! x; let J:= nX x; let A:= A! x; let H:= T! x; let Uρ:= A/S; let Qg:=g*Jets.Touch.chip L J; let Bq:=highR L J
    ∀ (P:BudgetPoint)(h:P.order=kF)(hp:P.power=pF)(hz:P.B=Bq)(he:P.threshold=U0),∀ M0:ℝ,∀ M1:ℝ,∀ e:ℝ,e∈Set.Icc 0 P.threshold → tK x*(v0^2) ≤ M0 → tK x*(U0*v0^2) ≤M1 → 0 < M0∧0 < M1 ∧
    Capital P nF nL kL a' b' M₀ (A/M0) Qg H (cleanA P nF iF M₀ At (A/M0) 1 v0) (cleanA P nF iF M₀ At (A/M0) 1 v0) Uρ ∧ Capital P nF nL kL a' b' cM (A/M1) Qg H (pl P nF iF M₀ At vT (A/M1) e v0) (pu P nF iF M₀ At vT (A/M1) e v0) Uρ:=by
       have hw := width_t L S nF kF pF nL kL iF vT At M₀ a' b' hΩ ht₀ he₀ ha hb hS0 he; filter_upwards [hw,ratio_v L he g hg] with x hx hc; dsimp only; intro P h hp hz hT M0 M1 e heA hv1 hv2; let A:=A! x; let T:= T! x; let u:= u! x; let f:= v! x; let E:=tK x; let b:=B x; let g0:=g*Jets.Touch.chip L (nX x); change E*f^2 ≤ _ at hv1; change E*(u*f^2) ≤_ at hv2
       obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩:=hc; have he₁:1 ≤E:= Surge.toll_pos _ _ _ _ _ _ _ _ _ _ _ hΩ ht₀ he₀ ha hb hS0
       have hq:E*(u*f^2)≤ M0:= ((mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right h3 (sq_nonneg f)).trans_eq (one_mul _)) (zero_le_one.trans he₁)).trans hv1)
       obtain ⟨hM1,hp1,hx1,he1⟩:=hx M1 hv2; obtain ⟨hM0,hp0,hx0,he0⟩:=hx M0 hq
       let A0:= A/M0; let A1:= A/M1; have hA:0 ≤ A0:= (div_pos h4 hM0).le; have hQ:0 ≤ A1:= (div_pos h4 hM1).le
       let W0:= Surge.cleanA P nF iF M₀ At A0 1 f; let H':= Surge.pl P nF iF M₀ At vT A1 e f; let V':= Surge.pu P nF iF M₀ At vT A1 e f
       let p0:= Surge.ubi P nF M₀ A0 g0 T W0; let p1:= Surge.ubi P nF cM A1 g0 T H'; let p2:= Surge.ubi P nF cM A1 g0 T V'; let θ:= V★ (B x)
       have hU0:(p0:ℝ) ≤ θ*A0*f^2:= Surge.trajectory nF kF pF iF vT At M₀ b hA hΩ ht₀ h1 he₀ (hT ▸ h3) h hp hz (by rw[hT]; exact h9) (by rw[hT]; exact h7)
       have hU:= Surge.trail_v (C:=g0) (G1:=T) (ξ:=A1) (P:=P) (t:=e) («v»:=f) nF kF pF iF vT At M₀ b hQ hΩ ht₀ h1 he₀ (hT ▸ h3) h hp hz (by rw[hT]; exact h9) (by rw[hT]; exact h7) heA.1 heA.2
       have hΨ(p r:ℝ)(h₀:0 ≤ p): 0 ≤ cleanA P nF iF M₀ At p r f:=by rw[fortune nF kF pF iF At M₀ b h hp hz]; exact mul_nonneg (mul_nonneg (pre_pos nF kF pF iF At M₀ b hΩ he₀) h₀) (sq_nonneg f)
       have htK: M₀ ≤cM:= le_add_of_nonneg_right (by positivity)
       refine ⟨hM0,hM1,Surge.rightCap nF kF pF nL kL iF vT At M₀ b A S M₀ _ g0 T h hp hz hΩ ht₀ he₀ ha hb hS0 (f^2) (sq_nonneg f) hM0 h4 htK hv1 hU0 h6 (hU0.trans he0) (ubi_nn hΩ hA (hΨ A0 1 hA) h5.le h8) hp0 hx0,?_⟩
       have ht1: p1 ≤ θ*A1*(u*f^2):=(hU.1).trans_eq (by rw[hT])
       exact Surge.rightCap nF kF pF nL kL iF vT At M₀ b A S cM _ g0 T h hp hz hΩ ht₀ he₀ ha hb hS0 (u*f^2) (by positivity) hM1 h4 le_rfl hv2 ht1 h6 (hU.2.trans he1) (ubi_nn (hΩ.trans htK) hQ (by unfold Surge.pl; apply add_nonneg; exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hQ (mul_nonneg (mul_nonneg ht₀ (sq_nonneg f)) P.threshold_pos.le)); exact mul_nonneg (by norm_num) (hΨ _ e (mul_nonneg heA.1 hQ))) h5.le h8) hp1 hx1
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.grantCap
