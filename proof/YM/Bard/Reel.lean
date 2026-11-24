import YM.Bard.Kite
import YM.Hypnos.Rider
import YM.Hypnos.EpochH
import YM.Hypnos.Optic
import YM.VStages.TotemW
import YM.VStages.Votaries
import YM.VStages.Through
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
variable {Δ:PlaqAxes}{μ' φ V' β:ℝ}
lemma callP (hi:i<n):|caller P₀ A X B T i| ≤ Vows (P.slope (A.node i)) N (A.spacing i) (A.beam i).fare:=by
   let V:= T.W.steps i hi
   let Q:= Y₁; let G:= Y₀; let M:= T.mesh i; let Z:= A.flight i; let S:= A.sail Q; let L:= A.spacing i; let αu:= stanceQ P₀ A i; let K':= (A.ticket i).applause
   have hT := V.birth; let D:= T.W.gauge i; let E:= T.W.spin i; let Y':= run (A.spacing i) (clockQ P₀ A x i)
   let R:= P.slope (A.node i)
   have hs': |D| ≤ |betaFare L R|:=by
      have he:= V.terrace.toll; have hf:= Gauge.slopeConstant_pos simple; have hg: 0≤ Real.log L.val:= Real.log_nonneg (by exact_mod_cast L.pos); apply (punctuate _ _ _ (show |D+su.slopeConstant*Real.log L.val| ≤ R from (le_add_of_nonneg_right zero_le_one).trans he)).trans; rw [abs_of_nonneg (mul_nonneg hf.le hg)]; apply le_trans _ (le_abs_self _); simp [betaFare,creditΓ,L]
   have hΩ: |D+(N:ℝ)*E|≤ Vows R N L (A.beam i).fare:=by
     have he:|E|≤((A.beam i).fare).b:= (V.birth.bill)
     refine (abs_add_le ..).trans ?_; rw [abs_mul,abs_of_nonneg (by positivity:(0:ℝ)≤N)]; exact le_trans (add_le_add hs' (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) (by positivity))) (by unfold Spire.Client.Vows; linarith)
   exact hΩ
variable (Z:Sheltered P₀ A X B T k Pt Δ) (V U W':ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable {κ:ℝ} (hE:Tavern P₀ A X B T κ Z V U W' F)(hc:entire P₀ A x Pt)
include hE
lemma jumpingV (hi:i<n):|V i-V (i+1)| ≤ Vows (P.slope (A.node i)) N (A.spacing i) (A.beam i).fare+2:=by
   let g:= caller P₀ A X B T i; have hx: |V i-V (i+1)-g|≤2:=(hE.relay i hi).step;
   calc _ = |g+(V i-V (i+1)-g)| := by congr 1; ring -- test
        _ ≤ _:= (abs_add_le ..).trans (add_le_add (callP P₀ A X B T hi) hx)
include hc
lemma forage (hi:i<n)(hD:HourV (P₀ (A.node i)) (X i) (clockQ P₀ A x i))(hx:1 ≤ speedP (A.spacing i) θ (q₀))(hK:Cairn.LitG (A.spacing i) θ (q₀) V' (Pt i) (A.ring (B.n k) i) F₀) : |W' i-1|≤16*Cairn.turfP (P₀ (A.node i)).U (A.spacing i) (q₀) N+16*V' :=by
    have hv:=hE.window (i+1) hi; have hT:=hE.relay i hi;  have hK':Cairn.LitG (A.spacing i) (X i).policy.t (q₀) V' (Pt i) (A.ring (B.n k) i) F₀:= by rw [(X i).theta]; exact hK
    exact currencyD P₀ A X B T Pt hD (hc i) (hc _) hv.2.1 hi hv.2.2.2.1 hT.real (by rw [(X i).theta]; exact hx) hK' _ hv.2.2.2.2 (Z.vetted i hi) (hT.lift ▸ hT.theoremG)
omit hE hc
lemma ticsV (A:ℝ)(L:Side)(N:ℕ): Rate su L (-1) (fun y=>16*Cairn.turfP A L y N +16*(run L y)⁻¹):=((chip_rate L|>.mul_left A|>.mul_left _).mul_left _).add ((show Rate su L (-1) (fun y=>(run L y)⁻¹) from by simpa only [Real.rpow_neg_one] using Rate.power (a:= -1) (G:=su) (L:=L)).mul_left _)
lemma greedV (hC:entire P₀ A x Pt)(j:ℕ)(p:ℝ)(hp:0<p):∀ᶠ c:Side in atTop, Cairn.LitG (A.spacing j) θ (clockQ P₀ A x j) p (Pt j) c F₀:=by
     have hV:(Pt j).supportExponent=2:= ((waking P₀ A (hC j)).era.2.2).trans (P.exponent _)
     exact Cairn.liftG _ _ _ _ _ _ hp hV
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.jumpingV
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.forage
