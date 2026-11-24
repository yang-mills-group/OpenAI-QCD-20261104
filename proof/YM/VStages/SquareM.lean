import YM.VStages.Through
import YM.QCD.Glass.Wave
import YM.QCD.Glass.Celebrate
import YM.QCD.Sq.Axis
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
variable {c f C F L:Side} {J:Patch} {j k k₀ n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j k₀}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open High PrismT MeasureTheory
open High PrismT MeasureTheory Sq
open Grass
lemma signsQ : Continuous (fun u:Grid f=> ater S h (F:=N) u):=by exact (Kit.choir_cont N).comp (tied_cont ..)
section pixels
variable {Dv : Set Twin}{bt :Twin→ℝ}{Ft:Twin→ Pixel f N}
lemma roomQ (hp:Reach Dv Ft):ContinuousOn (fun i:Twin×Grid f=> canQ S h N (Ft i.1) i.2) (Dv ×ˢ Set.univ):=by
    have he:ContinuousOn (fun p:Twin × Grid f=> Cove.light (Keys f N) (Ft p.1 p.2)) (Dv ×ˢ Set.univ):=(Cove.lightC _).comp_continuousOn (show ContinuousOn (fun p:Twin × Grid f=>Ft p.1 p.2) (Dv ×ˢ Set.univ) from hp)
    have hv := signsQ (S:=S) (h:=h) (N:=N); have hg: ContinuousOn (fun i:Twin × Grid f=> ater S h i.2 (F:=N)) (Dv ×ˢ Set.univ):= (Continuous.comp hv continuous_snd).continuousOn
    exact walksQ (fun (_:Twin) X=> ater S h X (F:=N)) (fun x U=> Cove.light _ (Ft x U)) _ Dv hg he (Kit.sheath_cont (b:=1))
lemma solarQ (hQ:IsClosed Dv)(hp: Reach Dv Ft)(hB:(S.visit K h).patch.Branches K su)(hv:ContinuousOn bt Dv):Reach Dv (fun i:Twin=> fortQ S K h N (bt i) (Ft i)):=by
     let M:= fun i:Twin=>canQ S h N (Ft i); have hz:=spinK (S.visit K h) M hQ (roomQ hp) hB hv; exact (levit c N).continuous.comp_continuousOn hz
end pixels
end Rails
end YM.QCD.Acre
