import YM.QCD.Vita.Ravine
import Mathlib.Topology.MetricSpace.Equicontinuity
import YM.Extraction.Tame
import Mathlib.Topology.UniformSpace.Ascoli
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Push.BetaTransport Rain MeasureTheory
variable {M Rᵥ V U Wᵥ A₁ Y:ℕ→ℝ}
open Topology
lemma ridge {X Y:Type*} [MetricSpace X][CompactSpace X][NormedAddCommGroup Y][ProperSpace Y] (F:ℕ→X→Y)(C:ℝ)(N:ℕ) (ht:∀ i:ℕ,N  ≤ i→ Continuous (F i))(he:∀ i:ℕ,N  ≤ i→∀ x,‖F i x‖ ≤ C)(hp:∀ ε:ℝ,0<ε→∃ δ:ℝ,0<δ∧∀ i:ℕ,N ≤ i→∀ x y, dist x y<δ → dist (F i x) (F i y)<ε) : ∃ f:ℕ→ ContinuousMap X Y, (∀ i:ℕ,N  ≤ i→f i=⟨F (max N i),ht _ (le_max_left _ _)⟩)∧IsCompact (closure (Set.range f)):=by
   let f : ℕ→ ContinuousMap X Y:= fun i=> ⟨F (max N i),ht _ (le_max_left _ _)⟩
   have hx: Equicontinuous ((fun a:ContinuousMap X Y => (a:X→Y)) ∘ ((↑) : Set.range f → ContinuousMap X Y)):=by
       intro a; apply Metric.equicontinuousAt_iff.mpr; intro ε hε; obtain ⟨δ,hδ,he⟩:=hp _ hε; refine ⟨δ,hδ,?_⟩; intro x hx i; obtain ⟨v,i,h⟩:= i; subst v; exact he (max N i) (le_max_left _ _) _ _ ((dist_comm a x).trans_lt hx)
   have hh := ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact (α:=X) (β:=Y)
   have h : ⋃₀ ({K : Set X|IsCompact K})=Set.univ:= Set.eq_univ_iff_forall.mpr (fun x=> Set.mem_sUnion.mpr ⟨Set.univ,isCompact_univ,Set.mem_univ x⟩)
   haveI : T2Space (UniformOnFun X Y {K|IsCompact K}):= UniformOnFun.t2Space_of_covering h
   refine ⟨f,fun _ _=>rfl, ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (ι:=ContinuousMap X Y) (F:=fun a=> (a:X→Y)) (𝔖:=setOf IsCompact) (fun _=>id) hh.isClosedEmbedding (fun K _=>hx.equicontinuousOn K) ?_⟩
   intro K h x hx; refine ⟨closedBall 0 C,isCompact_closedBall _ _,?_⟩; rintro _ ⟨i,rfl⟩; exact mem_closedBall_zero_iff.mpr (he _ (le_max_left ..) _)
variable {w y₁:ℝ}
lemma priceV (X:ℕ→Pixel c N)(Y:Pixel c N)(hx:∀ V,Tendsto (fun i:ℕ=>X i V) atTop (𝓝 (Y V)))(he:∀ᶠ i in atTop, Continuous (X i)∧∀ V, ‖X i V‖≤u) : Tendsto (fun i=> Cvol (X i)) atTop (𝓝 (Cvol Y)):= by
     let K:= peakW c N; refine tendsto_integral_filter_of_dominated_convergence (fun _=>‖K‖*u) ?_ ?_ (integrable_const _) (ae_of_all _ (fun i=> K.continuous.continuousAt.tendsto.comp (hx i)))
     · exact he.mono fun i hi=> ((K.continuous.comp hi.1).aestronglyMeasurable)
     exact he.mono fun i hi=> ae_of_all _ fun V=> (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hi.2 V) (norm_nonneg _))
lemma stance {X Y Z:Type}[TopologicalSpace X][TopologicalSpace Y][TopologicalSpace Z](p:X×Y→Z){A:ℕ→X}{B:ℕ→Y}{x y}(hp:Continuous p)(hx:Tendsto A atTop (𝓝 x))(hv:Tendsto B atTop (𝓝 y)):Tendsto (fun i=>p (A i,B i)) atTop (𝓝 (p (x,y))):= (hp.tendsto _).comp (hx.prodMk_nhds hv)
lemma tended (U₀:ℕ→Pixel f N)(X: Pixel f N)(he:∀ i,Tendsto (fun n:ℕ=>U₀ n i) atTop (𝓝 (X i)))(hv: Tendsto V atTop (𝓝 v))(hp: ∀ᶠ n in atTop, |V n|≤w ∧ Continuous (U₀ n) ∧ ∀ x,‖U₀ n x‖≤u)(hK:S.patch.Branches K su)(i:Grid c) : Tendsto (fun j=> advance S K h (U₀ j) (V j) i) atTop (𝓝 (advance S K h X v i)):=by
    let Y:= S.visit K h; obtain ⟨A,hA,hx⟩:=cans S h u N; refine tendsto_integral_filter_of_dominated_convergence (fun _=>noiseCost Y w*A) ?_ ?_ (integrable_const _) ?_
    · refine hp.mono fun n hh=>?_ ; exact (Y.push_slice (Y.isKernel hK (V n)) i _ ((tenderL S h _ hh.2.1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..))).1
    · refine hp.mono fun n hv=> ae_of_all _ fun i=>?_; rw [norm_smul]; -- defeq cast
      exact mul_le_mul ((le_of_eq (Real.norm_of_nonneg (Y.density_positive ..))).trans ((density_bounds Y hK hv.1 _ _).2)) (hx _ hv.2.2 _) (norm_nonneg _) (noiseCost_pos ..).le
    refine ae_of_all _ fun U=> Tendsto.smul ?_ ?_
    · let Y':= fun p:ℝ×Grid c=> Y.density p.1 U p.2; have ht:Tendsto (fun n=> (V n,i)) atTop (𝓝 (v,i)):=hv.prodMk_nhds tendsto_const_nhds; have hx:Continuous Y':=density_cont_all Y U
      exact stance Y' hx hv (show Tendsto (fun _:ℕ=> i) atTop (𝓝 i) from tendsto_const_nhds)
    have hh:= (he U); have hz:Tendsto (fun i=> (U,U₀ i U)) atTop (𝓝 (U,X U)):=Tendsto.prodMk_nhds tendsto_const_nhds hh; exact stance (Cane S h N) caneC (show Tendsto (fun _:ℕ=>U) atTop (𝓝 U) from tendsto_const_nhds) hh
lemma rightV (X:ℕ→Pixel c N)(Y:Pixel c N)(hp:Tendsto V atTop (𝓝 u))(hv:∀ x,Tendsto (fun i=>X i x) atTop (𝓝 (Y x)))(he:0<u)(i:Grid c): Tendsto (fun j=>gRight (X j) (V j) i) atTop (𝓝 (gRight Y u i)):=by
    have hz:= hp.inv₀ he.ne'; have hg:Tendsto (fun i=> (Rain.gain (V i)⁻¹ c N)⁻¹) atTop (𝓝 ((Rain.gain u⁻¹ c N)⁻¹)):= (hz.pow _).inv₀ (pow_ne_zero _ (inv_ne_zero he.ne')); have hX:Tendsto (fun j=> wearK c N (V j)⁻¹ (X j i)) atTop (𝓝 (wearK c N u⁻¹ (Y i))):= stance _ (conduct (c:=c) (N:=N)) hz (hv i); have hA:= (show Tendsto (fun j=>gBody c (V j) (X j i)) atTop (𝓝 (gBody c u (Y i))) from (Cove.lightC (Cove.Keys c N)|>.tendsto _).comp hX); exact hg.smul hA
end Rails
end YM.QCD.Acre
