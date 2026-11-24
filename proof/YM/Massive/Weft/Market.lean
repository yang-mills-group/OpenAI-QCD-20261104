import YM.Massive.Weft.Gear
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.QCD.Weft
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
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y0: Code c N) -- independent shape
set_option quotPrecheck false
variable (Y:Ruby.Hue c N Ω)(X:Gem c N I)(Q:Ruby.Hue c N I)(K: ℝ)
variable {g:Site c→ℂ}(L':I→Dye)(L0:Ω→ Dye)
open Ruby
open Warmlet
variable (E G :Gem c N I)(U:Grid c)(i:I)(w u:ℝ)
variable {E₀:Ruby.Hue c N I}(X:Gem c N Ω)
lemma residueHigh (hp:∀ i, qualified (L' i))(s:ℂ): farm E (serving L' 0 s)=0:=by
    have hh(i): serving L' 0 s i=0:=by unfold serving Struck.pigment; rw [zero_pow (Nat.ne_of_gt ((by norm_num:0<2).trans_le (hp i).2)),mul_zero]
    unfold farm; simp_rw [hh,zero_mul]; exact tsum_zero
lemma radiant (hp:Summable (fun i=>‖frost E i‖))(he:∀ i,Ash (L' i)):Fused (fun z s=>farm E (serving L' z s)):=by
    unfold farm; refine Fused.roll (fun i=> (prime _ (he i)).times (steady (frost E i))) hp (fun i z s hz hs=>?_); rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (upperPaint _ _ _ hz.le hs.le)
lemma hailH (U:Grid c)(v:ℂ)(ht:Summable (fun i=> Y.mean i U)): Calm.netT (wet Y fun _=> v) U=v • Calm.netT Y U:=(ht.hasSum.const_smul v).tsum_eq
lemma horizonNet (U:Grid c)(hs:Summable (fun i=>Y.mean i U))(hr:Summable (fun i=>Q.mean i U)): Calm.netT (HJoin Y Q) U=Calm.netT Y U+ Calm.netT Q U :=(teamed Q Y U (Calm.netT Y U) (Calm.netT Q U) hs.hasSum hr.hasSum).tsum_eq -- adjust
lemma wetJoin (f:Ω→ℂ)(P:I→ℂ): wet (HJoin Y Q) (Sum.elim f P)= HJoin (wet Y f) (wet Q P):=by
     unfold wet HJoin; congr! 1; ext i; rcases i with i|i<;>rfl
lemma serveJoin (z s:ℂ): serving (Sum.elim L0 L') z s = Sum.elim (serving L0 z s) (serving L' z s):=by funext i; rcases i with i|i<;>rfl
lemma netSum (z0 s0:ℂ)(hp:CostTall Y P t A r L0)(hr:CostTall Q P t A v L')(he:0≤A)(hf:1≤t)(hz:‖z0‖≤1)(hs:‖s0‖≤1):
   let w:= serving (Sum.elim L0 L') z0 s0; let Y':= serving L0 z0 s0; let D:= serving L' z0 s0; Calm.netT (wet (HJoin Y Q) w) U = Calm.netT (wet Y Y') U+ Calm.netT (wet Q D) U:=by
    intro w Y' D; unfold w; rw [serveJoin,wetJoin]; exact horizonNet _ _ _ (readable (wet Y Y') P.threshold U (wetted Y _ hp.tree) (wetCost Y Y' (fun i=>upperPaint _ _ _ hz hs) hp.budget) he hf).1 (readable (wet Q D) P.threshold U (wetted Q _ hr.tree) (wetCost Q D (fun i=>upperPaint _ _ _ hz hs) hr.budget) he hf).1
lemma qLowH (hp: Warm E (myLow I) X Y (myLow Ω) (myLow Ω) P t A K u w v)(ht:AgreesF E (myLow I) P.threshold):
  ∀U:Grid c, wearK c N v (Patron.total E P.threshold U) = Patron.total X P.threshold U+ Calm.netT Y U:=by
    intro U; let f:=fun _:Dye=>(1:ℂ); have hV:∀ i,‖f i‖≤1:=by simp [f]
    have hh:= hp.equal f U hV (ht f hV U); change wearK c N v (Patron.total (Library.wind E (fun _=>1)) P.threshold U) = _+ _ at hh; rw [nesting] at hh; rw [show Library.wind X (f∘myLow Ω)=X from nesting X,show wet Y _= Y from ?_] at hh; exact hh
    unfold wet; simp [f]
-- variants I Ω. use qLowH adjust
end YM.QCD.Weft
