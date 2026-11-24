import YM.Massive.Weft.Pledge
import YM.Massive.Weft.Operand
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
variable (G':Gem c N Ω)(X':Ruby.Hue c N Ω)(qℓ:ℝ) -- edit
variable (hp:Cargo E L' X G' Y X' L0 P t v A u w r K)
variable (hQ:0 ≤ K) (hs:1≤t)(hv:K+2≤A)
lemma faultLow (z:ℂ)(a:Flavor N):feeF a (z • (1:EvenA c N))=0:=by
    change Stew.meter _ _=_; have hu:Stew.meter a (1:EvenA c N)=0:= by
       have h:= Reggae.reducible (c:=c) a 1; rw [Reggae.gets,one_smul] at h; exact h
    rw [map_smul,hu,smul_zero]
lemma siteRead (z:ℂ)(Q:EvenA c N)(a:Flavor N): flagRead a t (z • 1+Q)=flagRead a t Q:=by rw [Finch.flagP,Finch.flagP]; rw [show feeF a (z • 1+Q)=feeF a Q from ?_]; change Stew.meter a _=(Stew.meter a Q); rw [map_add,show Stew.meter a (z • (1:EvenA c N))=0 from faultLow z a,zero_add]
lemma canopyLow (u v:ℝ)(g:EvenA c N)(i: Flavor N):flagRead i u (wearK c N v g)=v^2*flagRead i u g:=by unfold flagRead; rw [morn,mul_div_assoc]
include hp hs hv hQ
abbrev leaves (X:Gem c N I)(P:BudgetPoint)(f :Grid c) := Patron.total (Pith.rentGem (c:=c) (Pith.gaugeMass X)) P.threshold f + Patron.total (Pith.dusting X) P.threshold f
lemma vibe (b:Flavor N)(s:ℝ) : flagRead b s (Patron.total X P.threshold 1)=flagRead b s (leaves X P 1):=by
   have hT:= snowEq (myLow Ω) X u 1 hp.mass.pupil hp.mass.cost hv hs hQ; rw [hush (luminosity _ X u hp.mass.pupil hp.mass.cost (by linarith) hv hQ).tree,add_zero] at hT; unfold leaves; rw [hT,add_assoc,siteRead]
lemma leaseRead (s:ℝ)(f:Flavor N)(D:Gem c N I)(hD:E.view=D.view): flagRead f s (leaves X P 1) = v^2 *flagRead f s (Patron.total (LowSection D L') P.threshold 1):=by
   have he:= gr_y Y K L' L0 E w u X G' X' hp; rw [← vibe Y K L' L0 E w u X G' X' hp hQ hs hv f s,he,canopyLow]; rw [show Patron.total (LowSection D L') _ _=_ from (cooling (P:=P) (LowSection D L') (LowSection E L') ?_)]
   unfold LowSection; funext i; rw [eitherX,eitherX,hD]
end YM.QCD.Weft
