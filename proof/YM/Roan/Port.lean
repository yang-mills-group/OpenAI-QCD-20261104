import YM.Affina.Bears
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
lemma ruleV (hp:Fuel Wχ) : Rate su L 0 (fun x=>Wχ (B x)):=by -- copy
       obtain ⟨K,n,he,hK⟩:= hp.gains
       refine (Rate.weaken ((((opusR L).mul_left 8).pow n).mul_left K) (by simp)).compare ?_
       filter_upwards [heightR L] with x hx; exact (hK (B x)).trans (((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ((hx _ le_rfl).2) n) he)).trans (le_abs_self _))
lemma fireP :∀ᶠ x in atTop,0 < fiery su x L∧ fiery su x L ≤1 :=by
       filter_upwards [Delay.shift_pos su L,Rate.below (Rate.flame (G:=su) (L:=L)) (by norm_num) 1 zero_lt_one] with x hx hi; exact ⟨mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hx)) (Real.exp_pos _), (le_abs_self _).trans hi⟩
lemma city_b : Rate su L 0 (fun x=> wQ x) ∧ Rate su L 1 (fun x=>(u! x)⁻¹) ∧ Rate su L (-1) (fun x=> A! x) ∧ Rate su L (1/2) (fun x=>(u! x)⁻¹):=by
       have h:= roseR L (Blaze.inverse_mist su L) _ (Eventually.of_forall fun x=> show W x ≤ W x from le_rfl)
       refine ⟨((roseR L (Rate.rpow_monitor θ) _ (Eventually.of_forall fun i=>le_rfl)).pow _).weaken (by simp),h.weaken (by norm_num), roseR L (slotR L θ) _ (Eventually.of_forall fun _=>Nat.le_succ _), h⟩
lemma ratio_v (he:0<θ)(g:ℝ) (hg:0≤ g) :∀ᶠ x in atTop, let z:= nX x; let A:= A! x; let u:= u! x; let V:= T! x; let vh:=v! x; let w:= wQ x; 1 ≤ vh∧ 0<u∧ u≤1∧ 0 < A ∧ 0 < V∧ A/4 ≤ V ∧ V≤u*w ∧ g*Jets.Touch.chip L z∈ Set.Icc 0 (u*w):=by
      -- valuation subpower
      have hp: Rate su L (-(1/2)) (fun x=> g*Jets.Touch.chip L x*(fiery su x L)⁻¹):=((Jets.Touch.chip_rate _|>.mul_left _).mul (Blaze.inverse_mist su L)).weaken (by norm_num)
      have ht: Rate su L (-(1/2)) (fun x=> roomAt L θ x *(fiery su x L)⁻¹):=((slotR L θ).mul (Blaze.inverse_mist su L)).weaken (by norm_num)
      have h: Tendsto (fan L θ) atTop atTop:= (tendsto_rpow_atTop he).comp (Jets.Touch.Seat.your L); filter_upwards [aheadΩ L _ (fireP L),aheadΩ L _ (hp.below (by norm_num) _ zero_lt_one), aheadΩ L _ (ht.below (by norm_num) _ zero_lt_one), aheadΩ L _ (h.eventually_ge_atTop 1), aheadΩ L _ (shuttle L θ),aheadΩ L _ (event_chip L 1)] with x hx hh hr ht hp hg'; dsimp only
      let yS:= y x; let z:=nX x; let u:=u! x; let A:=A! x; let H:=T! x; have he:0 < u:=(hx _).1; have hZ:z=run L yS:=by unfold z yS riseV; push_cast; change x+_*_=x+ _* _+_; ring
      have hP:1 ≤ wQ x:=one_le_pow₀ (ht _); refine ⟨ht _,he,(hx _).2,(hp _).1,(hp _).1,?_, ?_, mul_nonneg hg ((hg' _).2.1.le), ?_⟩
      · change A/4 ≤ roomAt L θ z; rw[hZ]; linarith only [show A≤ 4*roomAt L θ (run L yS) from (hp _).2.1]
      · exact ((_root_.div_le_one he).mp (show H/u≤1 by rw[div_eq_mul_inv]; exact (le_abs_self _).trans (hr _))).trans (le_mul_of_one_le_right he.le hP)
      exact ((_root_.div_le_one he).mp (show (g*Jets.Touch.chip L z)/u≤1 by rw [div_eq_mul_inv]; exact (le_abs_self _).trans (hh _))).trans (le_mul_of_one_le_right he.le hP)
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
lemma width_t :∀ᶠ x in atTop,∀ M0:ℝ, tK x*(u! x*wQ x) ≤ M0 → 0 < M0∧ (hullP (B x) nF*(Real.exp (b₂+τ)*(cM*(P! x M0)*2^kF))≤τ)∧ Fp (B x)*(1+b'*a')*(A! x/S)*Sp (B x)* S ≤1∧ V★ (B x) * (P! x M0)*wQ x≤1:=by
       obtain ⟨hv,hr,hu,hX⟩:= city_b (θ:=θ) L
       let p:= fun x=> A! x * (u! x)⁻¹; have he': Rate su L (-(1/2)) p:= (hu.mul hX).weaken (by norm_num)
       obtain ⟨h,h₁,h₂,h₃⟩:= Surge.cost_traits nF kF pF nL kL iF vT At M₀; have hP := (((ruleV L _ h).mul he').mul hv).below (by norm_num) 1 zero_lt_one
       let f:=fun x=>Fp (B x) * (1+b'*a')* (A! x * S⁻¹) * Sp (B x)*S; have hz: Rate su L (-1) f:= (((((ruleV L _ h₂).mul_right _).mul (hu.mul_right S⁻¹)).mul (ruleV L _ h₁)).mul_right _).weaken (by norm_num)
       let bursa:=fun x=> hullP (B x) nF*(Real.exp (b₂+τ)*(cM*p x*2^kF)); have hh : Rate su L (-(1/2)) bursa:= ((ruleV L _ h₃).mul (((he'.mul_left _).mul_right _).mul_left _)).weaken (by norm_num)
       filter_upwards [hP,hz.below (by norm_num) _ zero_lt_one,hh.below (by norm_num) τ (by norm_num),ratio_v L he 0 le_rfl] with x hx hv hW hK A hA; obtain ⟨h1,h2,h3,h4,h5,h6,_⟩:= hK; have he₁:1 ≤ tK x:= Surge.toll_pos nF kF pF nL kL iF vT At M₀ (B x) S hΩ ht₀ he₀ ha hb hS0; have h :0≤cM:=by positivity
       have hU:u! x ≤ A:=((le_mul_of_one_le_right h2.le (one_le_pow₀ h1)).trans ((le_mul_of_one_le_left (show 0≤ u! x*wQ x from mul_nonneg h2.le (sq_nonneg _)) he₁).trans hA)); have ht':A! x/A≤ p x:= (div_le_div_of_nonneg_left h4.le h2 hU).trans_eq (div_eq_mul_inv _ _)
       refine ⟨h2.trans_le hU,?_,?_,?_⟩
       · apply (_ : _≤ bursa x) |>.trans ((le_abs_self _).trans hW); exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht' h) (by positivity)) (by positivity)) (show 0 ≤ hullP _ _ from by unfold hullP; positivity)
       · change MassiveQCD.Plate.Stags.bonus _ _ ε * _ * (_/S) * Basal.riseP _ _ _ ε b₁ * _ ≤ _; rw [div_eq_mul_inv ((A! x):ℝ) S]; exact (le_abs_self _).trans hv
       · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht' (Surge.supple nF kF pF iF vT At M₀ (B x) hΩ ht₀ he₀)) (sq_nonneg (v! x))).trans ((le_abs_self _).trans hx)
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.width_t
