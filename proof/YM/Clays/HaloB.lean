import YM.Clays.Pinot
import YM.Portland.Railing
import YM.Portland.District
import YM.Portland.Jolt
import YM.VStages.WindowY
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
variable {K:KernelChoices}
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
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open Affair
namespace Melt
open Weft Fibre Sway OrbitG Conductor Conductor.Quant Struck Struck.Library Aperture -- Weft
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)
variable (E:RiseBook P₀)
open Rails.Kin Massive.Filament
variable (M₀:Arrow N) {M₃:ℝ} (he:Views P₀ A X E x)
variable (Y:Precinct P₀ A B k n) (hh: Keeps P₀ A X B T V W F Y)
local notation "ζi"=> (clockQ P₀ A x i)
local notation "θ₀"=> θ
local notation "Fz0"=>family P₀ A B Y
local notation "Fz"=>family P₀ A B Y M₀.tip

namespace Lobby
open MassiveQCD.Plate MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Twist Bank
open Massive.Pressure Rails.Reference.Sharp
-- active point on gears
include he
variable {s w:ℝ}(C:DomeVoice P₀ A X B T V U W E M₀ Y Pt 0 s)
open scoped ComplexOrder
variable (Ht: Uptax P₀ A E x)(O:Paved P₀ A X x) (L1:HaarBudget su)
variable (hC:Glacier P₀ A X B T V U W E M₀ Y Ht C L1 w O)
local notation "DL" hi=> C.Λ i (Nat.zero_le _) hi
local notation "Fz!"=> family P₀ A B Y M₀.tip s
local notation "Tt"=> voyage P₀ A x w i
include hC
local notation "cp"=>A.ring (B.n k) i
local notation "fp"=>A.ring (B.n k) (i+1)
variable {Iq AA BB:Type} [Fintype Iq]
local notation "Θ"=> voyage P₀ A x w
local notation "qS"=> A.spacing i
local notation "vT"=>fan qS θ ζi
local notation "x⁺"=>run (A.spacing i) (clockQ P₀ A x i)
local notation "vT₁"=>fan qS θ x⁺
local notation "Ff"=>30*radiusB x⁺
local notation "Bn"=> Banner P₀ A X B T k Pt V
local notation "Sn"=> basisR P₀ A X B T k U
open Comet
local notation "Bz"=> maltar P₀ A X B T V U W E M₀ Y s w C
open Glint High.PrismT
local notation "vP"=> fan (A.spacing i) θ ζi
local notation "eV"=> Sharp.outE N (fees P₀ A E i) (dab P₀ A E i)
include hX
set_option maxHeartbeats 650000 in
lemma figureY (i:ℕ)(hi:i ≤ n)(R:BudgetPoint)(hq:(Pt i).B=R.B)(hz:(Pt i).threshold=R.threshold)(hN:R.order≤(Pt i).order)(hm:R.power≤(Pt i).power) : let s:=(C.Λ i (Nat.zero_le _) hi).EvalE (voyage P₀ A x w i); Licence R (1/8) (Sharp.outE N (fees P₀ A E i) (dab P₀ A E i)) (fan (A.spacing i) θ (clockQ P₀ A x i)) s∧∀ j,shadeG (s.view j):=by
     intro s'; obtain ⟨C',hPl⟩:= hC.enjoys i hi; have hB:= hPl.plank; unfold Shelf_R Banner basisR at hB; rw [field_flip P₀ A X B T] at hB
     obtain ⟨_, ht,h_t⟩:= orbitR P₀ A X E he i; let G:= HatWalk P₀ A B Y M₀.tip s x i; let L:= A.spacing i; let Z:= clockQ P₀ A x i; have hℓ:= (Ht.bill i).pos _ le_rfl; have hW:= hC.weight; have hF:0 ≤ w:=by linarith only [hW.1];
     let q:=voyage P₀ A x w i; have hh: ‖q‖ <1:= indoors P₀ A X E he w ((Real.norm_of_nonneg hF).trans_le hW.2) i; have hL:= gentYp (T':=twist (P:=P) (A.node i)) (J:= (A.flight i).patch) (U:=closing P₀ A X B T i) (J (A.level i)) F₀ M₀ L1 G (T.W.state i).path ht.outE ht.stampD (T.W.state i).wing hB hℓ.2.2.1.le hℓ.2.2.2.1 (waking P₀ A (hX i)).ball q hh
     let e:= Sharp.outE N (fees P₀ A E i) (dab P₀ A E i); have hE:0 ≤ e:=by unfold e Sharp.outE; have he:= Bank.Nimbus.forest N; positivity [ht.outE,ht.stampD]
     refine ⟨Tantra.renew s' hL hq hz hN hm (mul_le_of_le_one_right hE hℓ.2.2.2.1),?_⟩; let k':= (Rotary.chartR Z)⁻¹* cashR P₀ A x i w; have ht:q=(k':ℂ):=by unfold q k' Z voyage; push_cast; rw [classicR]; unfold cashR; push_cast; first|rfl|simp -- lhs? classicR read
     have hh0:= IV.blockPhase F₀ (C.Λ i (Nat.zero_le _) hi) hB.2.2.2.1.desk k'; have hg : CrossP s':= by unfold s'; change CrossP ((C.Λ i (Nat.zero_le _) hi).EvalE q); rw [ht]; exact hh0
     -- case rewrites dependent view index
     exact hg.gauge
-- temp
end Lobby
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.figureY
