import YM.Magi.Quartz
import YM.Profiles.Counts
import YM.Bard.York
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
open MassiveQCD.Cape
open Counter Melt.Lobby
section
-- explicit seed timing for β^tight through each roll. xg advance
variable {b':ChangeQ} (gT:Hypnos.State su)(b₆:ChangeQ)(C₆:Suburb P J b₆ θ N F₀ χ)
variable {S0:Flight b₆.old b₆.new}{p:ParcelR}{Θ σ Λ rTr:ℝ}(U:LedgerQ C₆ tol S0 Θ σ Λ p)
set_option quotPrecheck false
local notation "LV"=>S0.L
local notation "PC"=>S0.patch
local notation "EV"=>measureV LV
local notation "Bᵥ"=>run LV
open Rails.Reference.Sharp
abbrev thrifty (A:ℝ)(L:Side)(N:ℕ)(s:ℝ):= 16*Cairn.turfP A L s N+16*(run L s)⁻¹
lemma reserveV (A:ℝ)(L:Side)(N:ℕ):∀ᶠ x in atTop, thrifty A L N x ≤ cutOffV L (1/3) (run L x):=by
      have hh := ticsV A L N; have h₀ : Rate su L (-(1/2)) (fun x=> (2:ℝ)^((1/3):ℝ)*thrifty A L N x) :=(hh.mul_left _).weaken (by norm_num)
      filter_upwards [lapsV L 0,Delay.shift_pos su L,h₀ (-(1/3)) (by norm_num)] with x hx hv hz
      have ht:=hx 1 (by rw [distV,pow_zero]); rw [← slideV] at ht
      have h:= Real.rpow_le_rpow_of_nonpos (hv.trans_le ht.1) ht.2 (by norm_num: -(1/3:ℝ) ≤ 0)
      rw [Real.mul_rpow (by norm_num) hv.le] at h
      apply le_trans _ h; rw [Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]; rw [inv_mul_eq_div]; apply (le_div_iff₀ (by positivity)).2
      have hx: (2:ℝ)^((1/3):ℝ)*thrifty A L N x ≤ _:= (le_abs_self _).trans hz
      -- ring compare
      rw [mul_comm] at hx; exact hx
abbrev EK₁ (D ε:ℝ):= max 1 (outK D ε+1)
variable (l₁ l₂ bR l k m t d':ℕ)
structure PurseK (p:ℝ)(X:Patch)(v:ℝ)(F:ParcelR)(θ:ℝ)(N:ℕ)(D ε:ℝ)(l₁ l₂ l:ℕ)(x:ℝ) : Prop where
      sale : FoilV X.L x θ (ratioCostV X.L x) l₁ l₂ (MassiveQCD.Cape.orbital l) (EK₁ D ε)
      speed : 1 ≤ speedP X.L θ x
      budget : outK D ε+(taxK X.L x 1)⁻¹≤ EK₁ D ε
      rings : macroR X ≤ radiusB (run X.L x)
      forecast : ∀ β β':ℝ, run X.L (run X.L x) /2≤ β →β≤2*run X.L (run X.L x) → run X.L x/2≤β' →β'≤ 2*run X.L x→ |β'-β|≤feeS p N X.L F→
         |(gStep β)⁻¹| ≤gemmaV X.L (run X.L x)∧|(gStep β')⁻¹| ≤ gemmaV X.L (run X.L x)∧ |(gStep β)⁻¹-(gStep β')⁻¹|≤feeS p N X.L F
      earns : thrifty v X.L N x ≤ cutOffV X.L (1/3) (run X.L x)
      highX: 0<run X.L x
      upper: 0<run X.L (run X.L x)
      spanL: radiusB (run X.L (run X.L x)) ≤2*radiusB (run X.L x)
lemma stalks (p:ℝ)(X:Patch)(v:ℝ)(F:ParcelR)(θ:ℝ)(N:ℕ)(D ε:ℝ)(l₁ l₂ l:ℕ)(hθ:0<θ) : ∀ᶠ x in atTop, PurseK p X v F θ N D ε l₁ l₂ l x:=by
       let L:=X.L; have h:Tendsto (run X.L) atTop atTop:= E09.betaF_growth su _; have ht(n:ℕ):= (Pressure.radiusB); have hu:1≤ EK₁ D ε:=le_max_left ..
       filter_upwards [MassiveQCD.Cape.quarry L θ hθ l₁ l₂ (MassiveQCD.Cape.orbital l) (EK₁ D ε) (zero_lt_one.trans_le hu),Rails.latch L θ hθ N,reserveV v L N,h.eventually (marchingV L (feeS p N L F)),(Work.E01.radiusB_tendsto.comp h).eventually_ge_atTop (macroR X),cave L θ,(Work.E09.betaF_growth su L).eventually_gt_atTop 1] with x hp he hv hx hy hz ht
       have hT:1≤ taxK L x 1:=Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)
       let y:=run L x; have hY:run L x≤run L y:=le_add_of_nonneg_right (Work.E04.shift_nonneg su L); have h0:0< run L x:=lt_trans zero_lt_one ht; have hA:=hz.later
       refine ⟨hp,he.1,le_trans (add_le_add_right (inv_le_one_of_one_le₀ hT) _) (le_max_right ..),hy,?_,hv,h0,h0.trans_le hY,?_⟩ -- argument order
       · intro β β' hJ hK hk he ht; exact hx _ _ hJ hK (le_trans (half_pos h0|>.le) hk) (he.trans (mul_le_mul_of_nonneg_left hY (by norm_num))) ((abs_sub_comm ..).le.trans ht)
       change radiusB (run L y) ≤ _
       change (radiusB (run L y))^2 ≤ 2*(radiusB (run L x))^2 at hA
       by_contra h'; push Not at h'; nlinarith only [h',hA]
end
end Nimbus
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.Nimbus.stalks
