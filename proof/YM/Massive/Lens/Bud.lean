import YM.Massive.Lens.Height
import YM.Massive.Pith.Bill
import YM.Massive.Lens.Width
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
open Acre
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
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
namespace Library
variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y: Code c N) -- independent shape
set_option quotPrecheck false
namespace Carrier
variable {b:Flavor N}(φ:ℝ) (z s:ℂ)
abbrev rentalM (i:Flavor N):= φ⁻¹^2*Y.focus i
lemma rubyM (i: Site c × Flavor N)(U:Grid c): let B:=ampE Y.canonical (φ⁻¹^2); B.view i U=Pith.unitL i.2 (rentalM Y φ i.2) i.1:=by
   intro B; change (((φ⁻¹^2:ℝ):ℂ) • Pith.unitL i.2 (Y.focus i.2) i.1)=_; rw [Pith.Lscale,Pith.Lscale,Complex.coe_smul,smul_smul]
lemma learnsP (i:Site c × Flavor N) (U:Grid c): (Mast Y φ).main (spring Y i) U= Massive.Log.log (Pith.unitL i.2 (rentalM Y φ i.2) i.1):=by
   change (solvent (ampE Y.canonical (φ⁻¹^2)) (fun _=>pegE) 1 1).view (i,[]) U=_; rw [solvent_core]; change Massive.Log.log (off _ [] U)=_; rw [Lime.off]; exact congr_arg _ (rubyM Y φ i U)
lemma quarters (i:Site c×Flavor N): ((Mast Y φ).row (spring Y i)).support={i.1}:=rfl
variable {g_p: Site c× Flavor N →ℝ}
lemma earnG (i:Site c × Flavor N) (ht: LowFare (ampE Y.canonical (φ⁻¹^2)) P (1/8) t u g_p)(hx:u ≤1/8) (hp:1≤t): Stew.panel 2 ((Mast Y φ).main (spring Y i) 1).val=form (stripe N i.2 (localX i.1 ((rentalM Y φ i.2:ℂ) • 1))):=by
   rw [learnsP]; refine (visibleLog N (Pith.unitL ..) (mudLoan ..) ?_).trans ?_; rotate_left; · exact eachP N i.2 _ i.1 _ rfl
   let G:=ampE Y.canonical (φ⁻¹^2); let M:= (rentalM Y φ i.2); rw [← rubyM Y φ i (1:Grid c)]; refine ((sen_norm (o:=(G.addr i).site) t _ hp).trans ((ht.2 i).sizeU 1 (flat_ok ..))).trans_lt ?_; exact (anchored_each _ _ _ ht.1 (by norm_num : (0:ℝ)≤1/8) (fun i=>(ht.2 i).travel) i).trans_lt (hx.trans_lt (by norm_num : (1/8:ℝ)<1))
end Carrier
end Library
end YM.QCD.Struck
