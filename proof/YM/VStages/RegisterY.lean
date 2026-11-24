import YM.Massive.Moraine.Angle
import YM.VStages.Foster
import YM.VStages.PonderY
import YM.VStages.VistaW
import YM.Massive.Aperture.Calendar
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
open Massive.Filament
lemma ladDER (i:ℕ): (A.spacing i).val ≤ (A.spacing (i+1)).val:=by unfold Track.spacing; rw [A.length_eq i,A.length_eq (i+1)]; exact (A.nexts i).2.2.1
-- Consume in step i at χ(fine offset input)*dial i.
def dial (A:TrackQ (gate:=gate) P₀)(x:ℝ):ℕ→ℝ
  | 0=>1
  | i+1=> dial A x i * (Rotary.chartR (A.scale x i)) / Rotary.chartR (clockQ P₀ A x (i+1))

lemma clockQ_mono_rev (x:ℝ) (i:ℕ) : clockQ P₀ A x (i+1) ≤ A.scale x i:=by
   unfold clockQ; rw [engaged P₀ A]; unfold Spire.Client.fallback run betaF
   have hh : Real.log ((A.spacing i).val:ℝ)≤ Real.log ((A.spacing (i+1)).val:ℝ):= Real.log_le_log (Bloch.side_pos _) (by exact_mod_cast ladDER P₀ A i)
   linarith only [mul_le_mul_of_nonneg_left hh (Gauge.slopeConstant_pos simple).le]
variable (he:∀ i,1 ≤ clockQ P₀ A x i)
include he
lemma scaleRay (i:ℕ): 2<Rotary.chartR (clockQ P₀ A x i):= (Rotary.spring (A.spacing i) ((show 1 < (A.spacing i).val from (by have h:= (A.flight i).coarse; exact lt_of_lt_of_le (by norm_num) h))) _ (he i)).1
lemma scalePay (i:ℕ): 1≤ dial P₀ A x i:=by
   induction i with
   | zero=>exact le_rfl
   | succ i ih=>
       rw [dial]; apply (le_div_iff₀ ((by linarith only [scaleRay P₀ A he (i+1)]))).mpr; rw [one_mul]; have ht:= Spire.Moraine.rayMono (zero_lt_one.trans_le (he (i+1))) (clockQ_mono_rev P₀ A x i); exact ht.trans (le_mul_of_one_le_left ((by linarith only [scaleRay P₀ A he (i+1)] : 0 ≤ Rotary.chartR (clockQ P₀ A x (i+1))).trans ht) ih)
lemma scaleRay_eq (i:ℕ): dial P₀ A x i * Rotary.chartR (run (A.spacing i) (clockQ P₀ A x i)) = dial P₀ A x (i+1) * Rotary.chartR (clockQ P₀ A x (i+1)):=by
   rw [augmented,dial, div_mul_cancel₀]; exact ne_of_gt (by linarith only [scaleRay P₀ A he (i+1)])
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
