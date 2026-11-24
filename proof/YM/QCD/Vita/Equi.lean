import YM.QCD.Suns.Quality
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
lemma wheelDensity (S:StepData c f)(he:S.patch.Branches S.kernel su) (y:ℝ)(hp:0<ε):∃ u:ℝ,0<u∧∀ i:ℝ, |i|≤y→∀ U:Grid f,∀ V W:Grid c, dist V W <u → |S.density i U V - S.density i U W| ≤ ε:=by
    let T:=Set.Icc (-y) y ×ˢ (Set.univ:Set (Grid c × Grid c)); have hX : IsCompact T:= isCompact_Icc.prod isCompact_univ
    have hx : UniformContinuousOn (fun i:ℝ×Grid c ×Grid c=> S.noise i.1 i.2.1 i.2.2) T:= hX.uniformContinuousOn_of_continuous ((noise_cont_all S).continuousOn)
    obtain ⟨u,hu,hh⟩:= Metric.uniformContinuousOn_iff.mp hx ε hp; refine ⟨u,hu,fun i ht U V W hw=>?_⟩; have hz (Q:Grid c): |S.noise i Q V-S.noise i Q W| ≤ ε:=by
          have he : dist (i,Q,V) (i,Q,W)<u:=by simp [Prod.dist_eq,hw]
          have hp:= hh (i,Q,V) ⟨abs_le.mp ht,Set.mem_univ _⟩ (i,Q,W) ⟨abs_le.mp ht,Set.mem_univ _⟩ he; exact hp.le -- dist ℝ defeq?
    unfold StepData.density; rw [← sum_sub_distrib]; apply (abs_sum_le_sum_abs ..).trans; apply le_trans (b:=∑ t, S.likelihood U t * ε) (sum_le_sum ?_)
    · rw [← sum_mul, S.chosen he,one_mul]
    intro j _; rw [←mul_sub,abs_mul,abs_of_nonneg (S.likelihood_pos ..)]; exact mul_le_mul_of_nonneg_left (hz _) (S.likelihood_pos ..)
noncomputable def Cane (S:Flight j j)(h:f.val=c.val*S.L.val)(N:ℕ)(p: Grid f × EvenA f N):= Kit.sheath 1 (ater S h (F:=N) p.1) (Cove.light _ p.2)
lemma crossedG {X Y V W D:Type}[TopologicalSpace X][TopologicalSpace Y][TopologicalSpace V][TopologicalSpace W][TopologicalSpace D]{f:X→V}{g:Y→W} (U:V×W→D) (hc:Continuous f)(hv:Continuous g)(hp:Continuous U): Continuous (fun p:X×Y => U (f p.1,g p.2)):= hp.comp ((hc.comp continuous_fst).prodMk (hv.comp continuous_snd))
lemma caneC : Continuous (Cane S h N):=by
    exact crossedG (f:=fun i:Grid f=>ater S h (F:=N) i) (g:=fun z:EvenA f N=> Cove.light _ z) _ (signsR (S:=S) (h:=h)) (Cove.lightC _) (Kit.sheath_cont (b:=1))
lemma posedC {X Y Z:Type}[TopologicalSpace X][CompactSpace X][NormedAddCommGroup Y][ProperSpace Y][NormedAddCommGroup Z] (F:X×Y→Z)(hp:Continuous F)(v:ℝ):∃ T:ℝ,0<T∧∀ x y, ‖y‖≤v→‖F (x,y)‖≤T:=by
    let L:= (Set.univ:Set X) ×ˢ (closedBall (0:Y) v); obtain ⟨M,hM⟩:= (show IsCompact (L:Set (X×Y)) from isCompact_univ.prod (isCompact_closedBall _ _)).bddAbove_image hp.norm.continuousOn
    exact ⟨|M|+1,by positivity,fun x y hv=>(hM (show ‖F (x,y)‖∈ (fun i=>‖F i‖) '' L from ⟨_,⟨Set.mem_univ _,mem_closedBall_zero_iff.mpr hv⟩,rfl⟩)).trans ((le_abs_self _).trans (by linarith))⟩
lemma cans (S:Flight j j)(h:f.val=c.val*S.L.val)(H:ℝ)(N:ℕ):∃ T:ℝ,0<T∧∀ Z:Pixel f N,(∀ i,‖Z i‖≤ H) →∀ i, ‖can S h N Z i‖ ≤ T:=by
    obtain ⟨T,hT,hx⟩:=posedC (Cane S h N) caneC H; exact ⟨T,hT,fun Z hv i=>hx i (Z i) (hv i)⟩
lemma loft (S:StepData c f)(hv:S.patch.Branches S.kernel su)(A:ℝ)(hp:0<A)(N:ℕ)(y:ℝ) (he:0<ε):∃ t:ℝ, 0<t ∧∀ X:Grid f→Fields c N,Continuous X → (∀ i,‖X i‖ ≤ A) →∀ i:ℝ, |i|≤ y →∀ U V:Grid c,dist U V<t → dist (S.push i X U) (S.push i X V) ≤ ε:=by
     obtain ⟨t,ht,hh⟩:=wheelDensity S hv y (div_pos he hp); refine ⟨t,ht,fun X hX h i hw U V hV=>?_⟩; let k:=S.isKernel hv i; have hi(V:Grid c):=S.push_slice k V X (hX.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)) -- k implicits
     rw [StepData.push,StepData.push,dist_eq_norm,← integral_sub (hi U) (hi V)]
     refine (norm_integral_le_integral_norm _).trans ((integral_mono (g:=fun _=>ε) ((hi U).sub (hi V)).norm (integrable_const _) ?_).trans (by simp)); intro z; change ‖S.density i z U • X z-S.density i z V • X z‖≤ ε;  rw [← sub_smul,norm_smul]; exact (mul_le_mul (hh _ hw z _ _ hV) (h z) (norm_nonneg _) (by positivity : 0 ≤ ε/A)).trans_eq (div_mul_cancel₀ _ hp.ne')
-- Wave normalized with gain. Exact op.
noncomputable def warpH (c:Side)(N:ℕ)(t:ℝ)(Z:Fields c N):= wearK c N t (gain t⁻¹ c N • levit c N Z)
set_option synthInstance.maxHeartbeats 90000 in
noncomputable def crewH (c:Side)(N:ℕ)(t:ℝ): Fields c N →L[ℝ] EvenA c N:= (songT t).comp ((Rain.gain t⁻¹ c N) • ((levit c N).restrictScalars ℝ)) -- ok syntax
lemma warpR (V:Fields c N)(t:ℝ): warpH c N t V=crewH c N t V:=rfl
lemma walksU (t:ℝ)(ht:0<t)(Z:Fields c N): ContinuousAt (fun p:ℝ×Fields c N=> warpH c N p.1 p.2) (t,Z):=by
    unfold warpH
    let F(p:ℝ × Fields c N):= Rain.gain p.1⁻¹ c N
    have hv:ContinuousAt F (t,Z):=by
       have hv:ContinuousAt (fun p:ℝ × Fields c N=> p.1) (t,Z):=continuousAt_fst
       exact (hv.inv₀ ht.ne').pow _
    have hh:ContinuousAt (fun i:ℝ × Fields c N=> (i.1,F i • levit c N i.2)) (t,Z):=continuousAt_fst.prodMk (hv.smul ((levit c N).continuous.comp continuous_snd).continuousAt)
    let x:= F (t,Z) • levit c N Z; have he:ContinuousAt (fun i:ℝ × EvenA c N=> wearK c N i.1 i.2) (t,x):=conduct.continuousAt; exact he.comp (f:=fun i:ℝ × Fields c N=> (i.1,F i • levit c N i.2)) hh
lemma trusted (p:ℝ)(h:0<p):∃ U:ℝ,0<U ∧ ∀ t,t∈Set.Icc p 4→‖crewH c N t‖≤U:=by
    let Z:= crewH c N; let X:=Set.Icc p 4 ×ˢ (closedBall (0:Fields c N) 1)
    have hp: ContinuousOn (fun i:ℝ×Fields c N=> Z i.1 i.2) X:= fun i hi=> ((walksU i.1 (h.trans_le hi.1.1) i.2)).continuousWithinAt
    obtain ⟨M,hM⟩:= (show IsCompact X from isCompact_Icc.prod (isCompact_closedBall _ _)).bddAbove_image hp.norm; let V:=|M|+1; have he:0<V:=by unfold V; positivity
    refine ⟨V,he,fun t ht=> ContinuousLinearMap.opNorm_le_bound _ he.le (fun x=> ?_)⟩
    by_cases hx:x=0
    · rw [hx,map_zero,norm_zero,norm_zero,mul_zero]
    have hh:0< ‖x‖:= norm_pos_iff.mpr hx; let y:=‖x‖⁻¹ • x; have hy:‖y‖=1:=by unfold y; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hh).le, inv_mul_cancel₀ hh.ne']
    have hv : ‖Z t y‖ ≤ M:= hM (show _∈ _ from ⟨(t,y),⟨ht,mem_closedBall_zero_iff.mpr hy.le⟩,rfl⟩)
    have hz: V ≥ M:=by unfold V; linarith [le_abs_self M]
    change ‖Z t x‖ ≤ _; calc
       _ = ‖x‖ * ‖Z t y‖ :=by unfold y; rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hh).le,← mul_assoc,mul_inv_cancel₀ hh.ne',one_mul]
       _ ≤ _ :=by rw [mul_comm V]; exact mul_le_mul_of_nonneg_left (hv.trans hz) hh.le
abbrev SimpleH (S:Flight j j)(K:KernelChoices)(h:f.val=c.val*S.L.val)(x t:ℝ)(X:Pixel f N)(Y:Pixel c N):Prop:=∀ i, Y i= warpH c N t (advance S K h X x i)
lemma descent (S:Flight j j) (hK:S.patch.Branches K su)(h:f.val=c.val*S.L.val)(p s H:ℝ)(hp:0<p)(he:0<ε) :∃ δ:ℝ,0<δ ∧∀ (X:Pixel f N)(Y:Pixel c N), Continuous X → (∀ i,‖X i‖ ≤ H)→∀ x t:ℝ, |x| ≤ s→t∈Set.Icc p 4→ SimpleH S K h x t X Y→∀ i k:Grid c,dist i k <δ → dist (Y i) (Y k) < ε:=by
    obtain ⟨A,hA,hx⟩:= cans S h H N; obtain ⟨V,hv,hY⟩:= trusted (c:=c) (N:=N) p hp; obtain ⟨δ,hδ,ht⟩:=loft (S.visit K h) hK A hA N s (div_pos (half_pos he) hv); refine ⟨δ,hδ,fun X Y hg hZ x t hm hw hy i k hr=>?_⟩; rw [hy,hy,warpR,warpR]; have he':= (crewH c N t).lipschitz.dist_le_mul (advance S K h X x i) (advance S K h X x k);
    have hh:=ht _ (tenderL S h X hg) (hx X hZ) x hm i k hr
    exact he'.trans_lt (lt_of_le_of_lt (mul_le_mul (hY t hw) hh (dist_nonneg) hv.le) (by rw [mul_comm V, div_mul_cancel₀ _ hv.ne']; linarith))
end Rails
end YM.QCD.Acre
