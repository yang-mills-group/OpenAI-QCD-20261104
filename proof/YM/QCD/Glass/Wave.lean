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
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open High PrismT MeasureTheory
open High PrismT MeasureTheory Sq
open Grass
@[fun_prop] lemma conduct : Continuous (fun i:ℝ× EvenA c N=> wearK c N i.1 i.2):=by
   apply Topology.IsInducing.subtypeVal.continuous_iff.mpr; refine continuous_by_coef _ fun i=>?_; change Continuous (fun p: ℝ×EvenA c N=> coef i (engine p.1 (Keys c N) p.2.val)); simp_rw [fundW]; exact Continuous.mul (by fun_prop) ((continuous_coef i).comp (continuous_subtype_val.comp continuous_snd))
lemma signsR : Continuous (fun u:Grid f=> ater S h (F:=N) u):=by exact (Kit.choir_cont N).comp (tied_cont ..)
abbrev Reach {I:Type} [TopologicalSpace I] (D:Set I)(F: I→Pixel c N):Prop:=ContinuousOn (fun p:I×Grid c=>F p.1 p.2) (D ×ˢ Set.univ)
-- curry uses reduces whnf via typed theorem
lemma walksQ {I U V L R:Type}[TopologicalSpace I][TopologicalSpace U][TopologicalSpace V][TopologicalSpace L][TopologicalSpace R](F:I→U→V)(Q:I→U→L)(G:V×L→R)(D:Set I)(h:ContinuousOn (fun i:I×U=> F i.1 i.2) (D ×ˢ Set.univ))(hp:ContinuousOn (fun i:I×U=>Q i.1 i.2) (D ×ˢ Set.univ))(hv:Continuous G): ContinuousOn (fun i:I×U=>G (F i.1 i.2,Q i.1 i.2)) (D ×ˢ Set.univ):=hv.comp_continuousOn (h.prodMk hp)
lemma follows {Kx: Type}[TopologicalSpace Kx] {Dv:Set Kx} {Ft:Kx→Pixel c N}(hp:Reach Dv Ft){ts:Kx→ℝ}(hc:ContinuousOn ts Dv): Reach Dv (fun i=> vest c N (ts i) (Ft i)):=by
    have ht : ContinuousOn (fun i:Kx×Grid c=> ts i.1) (Dv ×ˢ Set.univ):=hc.comp' continuous_fst.continuousOn (fun _ i=> i.1)
    have hf:= walksQ (fun (i:Kx) (_:Grid c)=> ts i) Ft (fun p:ℝ×EvenA c N=>wearK c N p.1 p.2) _ ht hp conduct; exact hf
section pixels
variable {Dv : Set Twin}{bt :Twin→ℝ}{Ft:Twin→ Pixel f N}
lemma roomT (hp:Reach Dv Ft):ContinuousOn (fun i:Twin×Grid f=> can S h N (Ft i.1) i.2) (Dv ×ˢ Set.univ):=by
    have he:ContinuousOn (fun p:Twin × Grid f=> Cove.light (Keys f N) (Ft p.1 p.2)) (Dv ×ˢ Set.univ):=(Cove.lightC _).comp_continuousOn (show ContinuousOn (fun p:Twin × Grid f=>Ft p.1 p.2) (Dv ×ˢ Set.univ) from hp)
    have hv := signsR (S:=S) (h:=h) (N:=N); have hg: ContinuousOn (fun i:Twin × Grid f=> ater S h i.2 (F:=N)) (Dv ×ˢ Set.univ):= (Continuous.comp hv continuous_snd).continuousOn
    exact walksQ (fun (_:Twin) X=> ater S h X (F:=N)) (fun x U=> Cove.light _ (Ft x U)) _ Dv hg he (Kit.sheath_cont (b:=1))
lemma spinK {C: Type}[NormedAddCommGroup C][NormedSpace ℝ C][CompleteSpace C] (T:StepData c f)(G:Twin→ Grid f→ C)(hQ:IsClosed Dv)(he:ContinuousOn (fun p:Twin×Grid f=> G p.1 p.2) (Dv ×ˢ Set.univ))(hB:T.patch.Branches T.kernel su)(hv:ContinuousOn bt Dv): ContinuousOn (fun p:Twin×Grid c=> StepData.push T (bt p.1) (G p.1) p.2) (Dv ×ˢ Set.univ):=by
    have hh i (hi:i∈Dv): Continuous (G i):=continuousOn_univ.mp (he.comp' (continuous_const.prodMk continuous_id).continuousOn fun _ hu=>⟨hi,hu⟩)
    have hI i (hi:i∈Dv): Integrable (G i) (prior su f):= (hh i hi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
    obtain ⟨C,hc⟩:= ((IsClosed.isCompact hQ).prod isCompact_univ|>.bddAbove_image he.norm)
    let Z:=Dv ×ˢ (Set.univ:Set (Grid c)); intro p hR; change p∈Z at hR
    refine (Push.BetaTransport.push_continuousWithinAt T hB ((hv.comp' continuous_fst.continuousOn (fun (i:Twin× Grid c) (h:i∈ Z)=> h.1)) p hR) continuousWithinAt_snd (F:=fun (i:Twin×Grid c) U=> G i.1 U) (hI p.1 hR.1) (eventually_of_mem self_mem_nhdsWithin (fun i hi=>(hI i.1 (show i∈Z from hi).1).1)) ?_ (integrable_const C) ?_).2 -- hi.trans typo
    · apply ae_of_all; intro U; exact ((he.comp' (continuous_fst.prodMk continuous_const).continuousOn (fun (i:Twin×Grid c) (h:i∈ Z)=> ⟨h.1,(Set.mem_univ _)⟩)) p hR)
    filter_upwards [self_mem_nhdsWithin] with i hi; exact ae_of_all _ fun U=> hc (show ‖G i.1 U‖∈ (fun p:Twin×Grid f=> ‖G p.1 p.2‖) '' (Dv ×ˢ Set.univ) from ⟨(i.1,U),⟨hi.1,Set.mem_univ _⟩,rfl⟩)
lemma solarX (hQ:IsClosed Dv)(hp: Reach Dv Ft)(hB:(S.visit K h).patch.Branches K su)(hv:ContinuousOn bt Dv):Reach Dv (fun i:Twin=> fort S K h N (bt i) (Ft i)):=by
     let M:= fun i:Twin=>can S h N (Ft i); have hz:=spinK (S.visit K h) M hQ (roomT hp) hB hv; exact (levit c N).continuous.comp_continuousOn hz
end pixels
end Rails
end YM.QCD.Acre
