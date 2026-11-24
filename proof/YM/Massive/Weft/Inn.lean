import YM.Massive.Weft.Soft
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
variable (Y0: Code c N) -- independent shape
set_option quotPrecheck false
variable (Y:Ruby.Hue c N Ω)(X:Gem c N I)(Q:Ruby.Hue c N I)(K: ℝ)
variable {g:Site c→ℂ}(L':I→Dye)(L0:Ω→ Dye)
open Ruby
open Warmlet
variable (E G :Gem c N I)(U:Grid c)(i:I)(w u:ℝ)
lemma tokens (F:Grid c→ EvenA c N) (p:Support c)(hp:Grit F)(t:ℝ): Grit (masked t p F):=by
   constructor
   · intro i k; have h : Healthy t p (gauge k i) ↔ Healthy t p i:=by unfold Healthy; rw [gauge_flags]
     by_cases he:Healthy t p i
     · rw [masked_eq _ _ _ _ (h.2 he),masked_eq _ _ _ _ he]; exact hp.gauge i k
     rw [masked_ne _ _ _ _ (mt h.1 he),masked_ne _ _ _ _ he]; exact congr_arg Subtype.val (map_zero (sways (Lat.rotates N k)))
   · intro x; unfold masked Set.indicator; split; exact hp.flex x; exact phase_ite0
   intro x; unfold masked Set.indicator; split; exact hp.real x; exact map_zero _
lemma Grit_difference (F W:Grid c→EvenA c N)(hp:Grit F)(he:Grit W): Grit (F-W):=by
   refine ⟨fun U k=> ?_, fun U=> phase_sub (hp.flex _) (he.flex _), fun U=>(map_sub _ _ _).trans (congr_arg₂ Sub.sub (hp.real U) (he.real U))⟩; refine congr_arg Subtype.val (show sways (Lat.rotates N k) ((F-W) (gauge k U))=(F-W) U from ?_); exact (map_sub _ _ _).trans (congr_arg₂ Sub.sub (Subtype.ext (hp.gauge ..)) (Subtype.ext (he.gauge ..)))
lemma pointGrit (hp:Grit (E.view i))(he:E.view=G.view): Grit ((lira E G t).mean i):= by
    let H(X:Gem c N I):= masked t (X.addr i).support (X.view i); exact Grit_difference (H E) (H G) (tokens _ _ hp t) (tokens _ _ (congr_fun he i ▸ hp) t) -- replace
lemma permitGrit (hp: E.Gather)(hc:E.view=G.view)(hx:G.Gather)(_hm:∀ i,(G.addr i).site∈(E.addr i).support)(hψ:∀ i,(E.addr i).support ⊆(G.addr i).support)(f:I→ℝ)(hv:Valued G.addr (A+1+1) f P.B u)(h:∀ i U, ‖Loom.token c N t (letters E P.threshold U i)‖≤f i)(hA:0 ≤A):
   (lira E G P.threshold).Tall P.threshold ∧ SoftCost (lira E G P.threshold) P.B A (payment 1 (4*P.B+2) 0 1 1 u A 0) t:=by
    have hvG i U (h:Healthy P.threshold (G.addr i).support U) : (lira E G P.threshold).mean i U=0:= sub_eq_zero.mpr ((masked_eq _ _ _ _ (h.mono_left (hψ i))).trans ((congr_fun (congr_fun hc i) U).trans (masked_eq _ _ _ _ h).symm))
    refine ⟨⟨fun i U V w z=> congr_arg₂ (·-·) (Work.H03.reads_larger (hψ i) (clearUse E _ (hp.sees i) P.threshold) U V w z) (clearUse G _ (hx.sees _) P.threshold U V w z),fun i=> (RG.masked_measurable _ _ _ (hp.reads i)).sub (RG.masked_measurable _ _ _ (hx.reads i)),fun i U hn hp=> hn (hvG i U hp),fun i U=> wingsZ _ _ _ (gateMon _ _ (hψ i) _ (licit _ hp i U)) (licit _ hx i U)⟩,⟨f,tipped G f hv (vex G.addr f hv) le_rfl hA,fun i U=>?_⟩⟩
    by_cases hU:Healthy P.threshold (G.addr i).support U; · rw [hvG _ _ hU,map_zero,norm_zero]; exact vex G.addr f hv _
    change ‖Loom.token _ _ _ (_-letters _ _ _ _)‖≤_; rw [show letters G _ _ _=0 from masked_ne _ _ _ _ hU,sub_zero]; exact h i U
-- starting Gosh.Lights.First.Branch.All addresses. logistic.CornShelf.PhotoWear.
abbrev reFare (p:BudgetPoint)(X H:ℝ):= payment 1 (4*p.B+2) 0 1 1 X H 0
structure HitPack (E:Gem c N I)(P:BudgetPoint)(t σ u:ℝ):Prop where
    ready : ∃ f:I→ℝ,Ac.Hit (fun i=>(E.addr i).support) P.B f σ u∧∀ i,Woven (E.addr i).site (E.addr i).support P t (E.view i) (f i)
lemma widerT (D E:Gem c N I)(h0:Bigger D E (n*P.B))(hE:E.Gather)(hH:HitPack D P t σ u)(he:0≤r)(ht:(r+1+1)*(frostQ n) ≤ σ)(ht':0<t) :
     Licence P σ u t D ∧ (lira D E P.threshold).Tall P.threshold ∧ SoftCost (lira D E P.threshold) P.B r (reFare P u r) t :=by
     obtain ⟨p,h,p₀⟩:= hH.ready; have hσ(i):0 ≤ p i :=(p₀ i).travel; have hp:Licence P σ u t D:=⟨p,anchorM D p hσ h,p₀⟩; refine ⟨hp,permitGrit D E u (Entr.Licence_g hp) h0.view.symm hE (fun i=>(h0.bump i).1) (fun i=>(h0.bump i).2.1) _ (tiller h hσ (fun i=>(h0.bump i).1) ?_ (by linarith : 0 ≤ r+1+1) ht) ?_ he⟩ -- expand
     · intro i; rw [mul_comm]; exact_mod_cast (show coverNumber P.B _ ≤ coverNumber P.B (D.addr i).support*frostQ n from (Corona.cover_mono (h0.bump i).2.2 P.B).trans (touring _ n _ P.B P.B_pos le_rfl))
     intro i U; by_cases hf:Healthy P.threshold (D.addr i).support U; · unfold letters; rw [masked_eq _ _ _ _ hf]; exact (Stem.opticX _ _ _ ht').trans ((p₀ i).sizeU _ hf)
     rw [letters,masked_ne _ _ _ _ hf,map_zero,norm_zero]; exact hσ _
end YM.QCD.Weft
