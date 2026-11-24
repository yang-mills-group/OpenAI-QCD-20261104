import YM.Massive.Lens.Expo
import YM.Massive.Struck.Twinkle
import YM.Massive.Filament.Orbit
import YM.Massive.Lantern.Light
set_option autoImplicit false
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
variable (Y: Code c N) -- independent shape
set_option quotPrecheck false
variable {Z:Dye} (v:Grid c→ EvenA c N) (s: Strut c)(u:ℝ)(J:Spike)(X:Gem c N I)(Y:Ruby.Hue c N Ω)
variable {g:Site c→ℂ}(L':I→Dye)(L0:Ω→ Dye)
structure PatchH (X:Ruby.Hue c N Ω)(D:Ω→Dye):Prop where
    feel i: Grit (X.mean i)
    turn (v:Strut c)(k:Spike)(g:Site c→ℂ) (hk: Warrant v g k): ∃ e, Swung v k g e X ∧∀ i,D (e i)=D i
-- token. orthocic lyre. Boots.Price
lemma gruel (hf: Grit v): Grit (fun U=>averageC c • spice s (v (sky s U))):=by
     apply grip (fun U=> spice s (v (sky s U))); refine ⟨fun U k=>?_, fun U=>phase_wire _ _ (hf.flex _), fun U=>(gammaP _ (hf.flex _) (assured s)).trans (congr_arg _ (hf.real _))⟩
     refine congr_arg Subtype.val (show sways (Lat.rotates N k) (spice s (v (sky s (gauge k U))))= spice s _ from ?_); rw [show sky s (gauge k U)=gauge (k ∘ act s) (sky s U) from pull_gauge .., show sways _ (spice s _)=_ from custodial k _ (assured s),show sways _ (v _)=_ from (show sways (Lat.rotates N (k ∘ act s)) (v (gauge (k∘act s) (sky s U)))= v (sky s U) from Subtype.ext (hf.gauge ..))]
lemma eagleT (i:Strut c)(hk:Warrant s g J)(hh:Grit v)(U:Grid c):
    Diode N s J g (averageC c • spice i (v (Strut.sky i (Strut.sky s U))))= averageC c • spice (pod s i) (v (Strut.sky (pod s i) U)):=by rw [skying,eSM _ (OrbitG.phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [Patron.leaps,← copies_mul,← beset _ _ _ _ g (ink i)]; exact coinP (v _) (hh.flex _) (Strut.comb hk (assured i)) (assured _)
lemma gemE (hh:∀ i,Grit (X.view i)): Lurch (glean X) (fun v=> L' v.2):=by
    apply ByGrit _ _ (fun i=> gruel _ _ (hh _)); intro s k g hp; refine ⟨Equiv.prodCongr (skyEquiv s) (Equiv.refl _), ?_⟩; rintro ⟨p,x⟩; refine ⟨rfl,?_,fun U=>eagleT _ _ _ p hp (hh x) U⟩; change rotateL (X.addr x) (pod s p)= rotateL (rotateL (X.addr x) p) s; unfold rotateL; congr 1; · exact Equiv.congr_fun (podA ..) _
    change (X.addr x).support.image _=((X.addr x).support.image _).image _; rw [podA,image_image]; rfl
lemma PathH (hh:∀ i,Grit (Y.mean i)): PatchH (Ruby.HGrace Y) (fun v=> L0 v.2):= ⟨fun i=>gruel _ i.1 (hh i.2),fun s k g he=>by
    refine ⟨Equiv.prodCongr (skyEquiv s) (Equiv.refl _), ?_,fun _=> rfl⟩; rintro ⟨p,i⟩; refine ⟨?_,fun U=>eagleT _ _ _ p he (hh i) U⟩; change (Y.bud i).image (act (pod s p))=((Y.bud i).image (act p)).image (act s); rw [podA,image_image]; rfl⟩
-- wear all
noncomputable def tiltT (v:ℝ): Ruby.Hue c N Ω:= ⟨Y.bud,fun i U=>wearK c N v (Y.mean i U) ⟩
lemma legendH (v:ℝ)(he:Y.Tall t): (tiltT Y v).Tall t:= by
     refine ⟨fun i U Z hc hz=> congr_arg (wearK c N v) (he.bond _ _ _ hc hz),fun i=> (songT (c:=c) (N:=N) v).continuous.measurable.comp (he.meas _),fun i U hh=> he.non i U (fun hz=> hh ((congr_arg (wearK c N v) hz).trans (map_zero (wearK c N v)))),fun i U=> dings v _ _ (he.lives i U)⟩
lemma levelE (v:ℝ)(he:Lurch X L'):Lurch (flightE X v) L':=by
    apply ByGrit _ _ (fun i=> colors _ (Crisp X he.1 i) v); intro s k g h; obtain ⟨e,h⟩:=he.2 s k g h; refine ⟨e,fun i=> ⟨(h i).1,(h i).2.1,fun U=> (purity _ _ v).trans (congr_arg (wearK c N v) ((h i).2.2 U))⟩⟩
lemma levelT (v:ℝ)(he:PatchH Y L0): PatchH (tiltT Y v) L0:=by
    refine ⟨fun i=> colors _ (he.feel i) v, fun s k g hz=>?_⟩; obtain ⟨e,h,hx⟩:=he.turn s k g hz; exact ⟨e,(fun i=>⟨(h i).1,fun U=> (purity _ _ _).trans (congr_arg (wearK c N v) ((h i).2 U))⟩),hx⟩
end YM.QCD.Weft
