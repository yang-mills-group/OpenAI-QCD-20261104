import YM.VMarker.Spell
import YM.MassiveQCD.Plate.Coined
import YM.Massive.Conductor.Mount
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Conductor
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
variable (X:ℂ→ℂ→ Patron.Rail c N I)(Y:ℂ→ℂ→Ruby.Hue c N Ω)
open Ruby Weft High
set_option quotPrecheck false
local notation "Tz"=>P.threshold
variable {b Y₁: ℝ}{s z U:ℂ}
local notation "νT"=> (1/8:ℝ)
open Meridians Rails.Bank
-- E+K harmonics. finite count arguments vs existence of Budget.Meta.R
variable {b':Flavor N} {s0:ℂ}
variable (V: Gem c N ι) (Z:ι→ Dye) (E G:Gem c N Ω)(Q Q':Ruby.Hue c N Ω)(p':Ω→Dye)
variable (φ κ W₀ W₁:ℝ)
variable (D₀:Voice c N)
variable [aΩ:Countable Ω][aI:Countable I]
-- substitution at frozen step.
open MassiveQCD.Plate
namespace Tandem
variable {K₀ I₁:Type}
omit aI in
lemma transM (x:Patron.Rail c N I)(y:Patron.Rail c N I₁)(Z:Patron.Rail c N K₀)(hp:Correspond x y)(he:Correspond y Z): Correspond x Z:= ⟨hp.pays,he.coins,fun H V=>(hp.governs H V).trans (he.governs H V)⟩
open Rails.Links
omit aI in
lemma payment (X:Patron.Rail c N I) (Y: Patron.Rail c N I₁) (Z:Patron.Rail c N K₀) (hp:toEnv X=toEnv Y)(he:Correspond X Z): Correspond Y Z:= Eq.mp (congr_arg (fun A:Envelope c N => Correspond A.snd Z) hp) he
section motion
-- each card i presents countably partition of original support. reassemble at Hat
variable (F:Patron.Rail c N I)(X:Patron.Rail c N I₁)(π:I→ I₁)(he:∀ i,F.addr i=X.addr (π i))(hz:∀ U,Summable (fun i=> ‖F.warp i U‖))(hX:∀ U,Summable (fun i=> ‖X.warp i U‖))(hV:∀ i U, HasSum (fun j:I=> if π j=i then F.warp j U else 0) (X.warp i U))
include he hz hX hV
omit aI in
lemma fromT : Correspond X F :=by
    refine ⟨hX,hz, fun H V=>?_⟩
    let p(i:I):= if F.addr i=H then F.warp i V else 0
    have hf : Summable p:= (hz V).of_norm.indicator {i |F.addr i=H}
    have hh(i:I₁): (∑' j:π ⁻¹' ({i}:Set I₁), p j.val)= if X.addr i=H then X.warp i V else 0:=by
         split
         next h=> apply Eq.trans (b:= ∑' j:π ⁻¹' ({i}:Set I₁), F.warp j.val V) (tsum_congr fun j=>if_pos ((he j.val).trans (show X.addr (π j.val)=H from (congr_arg _ (show π j.val=i from j.2)).trans h))) _; apply Eq.trans (_root_.tsum_subtype (π ⁻¹' ({i}:Set I₁)) (fun j:I=> F.warp j V)); convert (hV i V).tsum_eq; simp [Set.indicator]
         next hv=> rw [tsum_congr (f:=fun j:π ⁻¹' ({i}:Set I₁)=>p j.val) (g:=fun _=>0) (fun j=> if_neg (by rw [he,show π j.val=i from j.2]; exact hv)),tsum_zero]
    simp_rw [fingerprint]; exact (tsum_congr fun i=> (hh i).symm).trans ((hf.hasSum.tsum_fiberwise π).tsum_eq)
end motion
variable {z:ℂ}
variable (he: Meridians.Seed X P (taxK L x 4) (3/16) (fan L η x) s0)
variable (ht:1≤fan L η x)(hκ:0 ≤ κ)(hs: Safe (φ:ℂ))(hx:κ<1)
variable (hr: P.B=highR L x)(hD: Enn P b' L x η νT (deckH D₀))
variable (hk:Quits (faint X 1 κ φ) P.B u (taxK L x 1) νT (fan L η x))(hK:Quits (Fibre.tail X κ φ) P.B w (taxK L x 1) νT (fan L η x))(hz:‖s0‖<1)
local notation "D₁"=> fan L η x
include he ht hκ hs hx hr hD hk hK hz aΩ
lemma mounted_link (z:ℂ) (h:‖z‖≤1) :
  let S:= X ((κ:ℂ)*z) φ; let Y:= mounted X E G p' φ κ D₀; Y.EvalE z=payWarp D₀ E G p' ((κ:ℂ)*z) φ ∧ Correspond S (Y.EvalK z):=by
    intro S Y; let a:ℂ:= (κ:ℂ)*z; let T:= Harm.flux X κ φ z; have h1:= Conductor.near κ hκ hx z h; have hs':= Fused.withinL hs; obtain ⟨_,hq⟩:= tenorOne X he D₀ hD hr rfl hz
    have hp Tt (H:0 ≤ Tt) :1 ≤ taxK L x Tt:=Real.one_le_exp (mul_nonneg H (fan_pos L (1/3) x).le)
    have hF : ∀ V,Summable (fun i=> ‖T.warp i V‖):=ensures T (Harm.factorTie _ _ _ _ hq hk hK h) (hp 1 (by norm_num)) (by norm_num:0≤νT) ht
    refine ⟨?_,fromT T S Harm.peak ?_ hF ?_ ?_⟩
    · refine congr_arg (weave D₀.P) (congr_arg₂ weave ?_ (congr_arg₂ weave (windL _ φ κ z) (windH G p' φ κ z)))
      change Library.wind (Pith.rentGem (c:=c) (fun i=> φ^2*κ*(gaugeMass E i))) _=_; rw [← clearsL]; exact windL _ φ κ z
    · intro i; unfold S; rw [he.prag.brace]; cases i with| inl i=> rfl| inr i=>cases i<;> rfl
    · exact ensures S (he.scene a φ h1.le hs'.le).spends (hp 4 (by norm_num)) (by norm_num) ht
    intro i V; exact Harm.affirms X κ V he.prag hs' h1 (fun i=> (hF V).of_norm.indicator {j | Harm.peak j=i}) i
end Tandem
end YM.QCD.Conductor
#print axioms YM.QCD.Conductor.Tandem.mounted_link
