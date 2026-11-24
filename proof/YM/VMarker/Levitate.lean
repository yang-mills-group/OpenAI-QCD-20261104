import YM.Massive.Struck.Puff
import YM.MassiveQCD.Plate.Coupons
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
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
namespace Library
namespace Levitate
open Sway Pith Lime Ruby Strut
instance (c:Side):Countable (Cove.Hat c) := Injective.countable (f:=fun i:Cove.Hat c=> (i.place,i.inv)) (by rintro ⟨i,m,h,e⟩ ⟨j,n,h',e'⟩ H; cases Prod.mk.inj H with|intro h₁ h₂=> rcases h₁,h₂ with ⟨rfl,rfl⟩; rfl)
abbrev PX (c:Side):= RegularAddress c × ℕ
abbrev KY (c:Side):= Cove.Hat c × ℕ
variable (X:Patron.Rail c N I)
noncomputable def stampE (w:Equiv.Perm (Site c))(x:RegularAddress c):RegularAddress c:=⟨w x.site,x.support.map w.toEmbedding, mem_map.mpr ⟨_,x.anchor,rfl⟩⟩
noncomputable def stampK (w:Equiv.Perm (Site c))(x:Cove.Hat c):Cove.Hat c:=⟨x.place.map w.toEmbedding,x.inv.map w.toEmbedding,x.alive.map, map_subset_map.mpr x.part⟩
lemma rot_t (w:Equiv.Perm (Site c))(x:RegularAddress c): stampE w.symm (stampE w x)=x:=by cases x; unfold stampE; simp [Finset.map_map, show w.toEmbedding.trans w.symm.toEmbedding=Embedding.refl _ from Embedding.ext (by simp)]
lemma rot_u (w:Equiv.Perm (Site c))(x:Cove.Hat c):stampK w.symm (stampK w x)=x:=by cases x; unfold stampK; simp [Finset.map_map, show w.toEmbedding.trans w.symm.toEmbedding=Embedding.refl _ from Embedding.ext (by simp)]
noncomputable def ampE (w:Equiv.Perm (Site c)):Equiv.Perm (RegularAddress c):= ⟨stampE w,stampE w.symm,rot_t w,rot_t w.symm⟩
noncomputable def ampK (w:Equiv.Perm (Site c)):Equiv.Perm (Cove.Hat c):=⟨stampK w,stampK w.symm,rot_u w,rot_u w.symm⟩
noncomputable def voidE (c:Side)(N:ℕ):Gem c N (PX c):=⟨Prod.fst,0⟩
abbrev dead (c:Side):PX c→ℕ:=fun _=> 2
noncomputable def cloakY : Patron.Rail c N (I⊕KY c):=⟨Sum.elim X.addr Prod.fst,Sum.elim X.warp (fun _=>0)⟩
variable {b:Flavor N}{t:ℝ}
private lemma zeroG : Grit (0:Grid c→EvenA c N):=by
    refine ⟨?_,fun _=>phase_ite0,fun V=>map_zero _⟩; intro U g; change Lat.slots N g (Cove.light _ 0)=Cove.light _ 0; rw [map_zero,map_zero]
noncomputable def talc (X:Code c N): Code c N := {X with high:=weave X.high (voidE c N), B:=X.B⊕PX c, ad:=Sum.elim X.ad (dead c), E:=X.E⊕KY c, prime:=cloakY X.prime,b0:=inferInstance,e0:=inferInstance}
-- Casement of rotations
lemma coreL (h:X.Reg t): (cloakY X).Reg t:=by
    constructor
    · rintro (i|i); exact h.uses i; intro _ _ _ _; rfl
    · rintro (i|i); exact h.reads i; exact measurable_const
    · rintro (i|i) V; exact h.role i V; change Cove.light _ (0:EvenA c N)∈_; rw [map_zero]; exact Subalgebra.zero_mem _
    rintro (i|i) V; exact h.buys i V; exact fun h=>(h rfl).elim
lemma chalk (Y:Code c N)(h:Desk Y P b L x η) : Desk (talc Y) P b L x η:=by
    let R:=talc Y
    have hb (s:Strut c)(k:Spike)(g:Site c→ℂ)(hk:Warrant s g k): ∃ e:Equiv.Perm R.B,∀ i,R.ad (e i)= R.ad i∧R.high.addr (e i)= rotateL (R.high.addr i) s∧∀ U, Diode N s k g (R.high.view i (sky s U))= R.high.view (e i) U:=by
        obtain ⟨e,he⟩:=h.carries s k g hk; refine ⟨ Equiv.sumCongr e (Equiv.prodCongr (ampE (act s)) (Equiv.refl _)),?_⟩; rintro (i|i); exact he i; refine ⟨rfl,?_,fun _=>map_zero _⟩; change stampE _ _=rotateL ..; unfold stampE rotateL; congr 1; rw [Finset.map_eq_image];rfl
    refine ⟨h.base,h.arg, ⟨?_,?_,?_,fun v k g hv=>?_⟩,⟨?_,?_⟩,h.wish,coreL _ h.low,h.high, ?_,h.star,hb,h.rises⟩
    · rintro (i|i); exact h.eve.gauge i; exact zeroG.gauge
    · rintro (i|i); exact h.eve.num i; exact zeroG.flex
    · rintro (i|i); exact h.eve.real i; exact zeroG.real
    · obtain ⟨e,he⟩:=hb _ _ _ hv; exact ⟨e,fun i=>(he i).2⟩
    · rintro (i|i); exact h.warm.tone _; exact zeroG
    · intro p k g hv; obtain ⟨e,he⟩:=h.warm.turn _ _ _ hv
      refine ⟨ Equiv.sumCongr e (Equiv.prodCongr (ampK (act p)) (Equiv.refl _)),?_⟩; rintro (i|i); exact he i; exact ⟨Finset.map_eq_image ..,Finset.map_eq_image ..,fun _=>map_zero _⟩
    rintro (i|i); exact h.bottom i; exact le_rfl
open Carrier MassiveQCD.Plate
lemma income_v (hp:Quits X n A x r t): Quits (cloakY X) n A x r t:=by
    let Y:=cloakY X; obtain ⟨f,h,hf⟩:=hp.cost; let g:= Sum.elim f (fun _:KY c=> (0:ℝ)); refine ⟨g,?_,?_⟩; · intro i; rw [← add_zero A]; let p(i:KY c):= if i=i then (0:ℝ) else 0; apply Fibre.budgetFuse <;> first| exact h i| refine ⟨fun _=>?_,?_,?_⟩ <;> change _ <;> simp [cloakY,g,taxed, oriD,Ruby.home,Function.comp_def] -- notation
    rintro (i|i) V; exact hf i V; change ‖Loom.token c N t 0‖ ≤0; rw [show Loom.token _ _ _ 0=0 from map_zero _,norm_zero] -- tweak.
lemma slips_v (P:BudgetPoint)(o:RegularAddress c)(t:ℝ)(hp:0<t): Woven o.site o.support P t (0:Grid c→EvenA c N) 0 ∧ Reggae.mud ( (0:EvenA c N))=0 ∧ (Nonwrapping o.support o.site→ Fleck P o.support o.site false (0:Grid c→EvenA c N) t 0):=by
    have hz:Reggae.mud (0:EvenA c N)=0:=map_zero (clay c N); exact ⟨Loom.Wzero t,hz,fun ho=> puff o.site zeroG (Loom.Wzero t) ⟨hz,fun _ h=>False.elim (Bool.noConfusion h)⟩ hp ho o.anchor⟩ -- args
variable (Y:Code c N) {tM uM:ℝ}
set_option quotPrecheck false
local notation "ζY"=> talc Y
lemma silt (hf:Fare Y P L x η A D): Fare (talc Y) P L x η A D:=by
    refine ⟨hf.low,?_, income_v _ hf.near,hf.top⟩; obtain ⟨f,h,H⟩:= hf.high; let g:= Sum.elim f (fun _:PX c=>(0:ℝ)); refine ⟨g,fun i=>?_,?_⟩
    · rw [←add_zero D]; apply Fibre.budgetFuse; · exact h i
      refine ⟨fun _=>?_,?_,?_⟩ <;> simp [g,Function.comp_def]
    rintro (i|i); exact H i; exact slips_v P _ _ (fan_pos ..)
-- Cash alignment independently of normal.E. Tagged E log array handled via availability of donor. 
noncomputable def mapV : Y.master.ι⊕(Site c×Flavor N)⊕Y.A⊕Y.B ↪ Y.master.ι⊕(Site c×Flavor N)⊕Y.A⊕(Y.B⊕ PX c):= ⟨Sum.map id (Sum.map id (Sum.map id Sum.inl)), Sum.map_injective.mpr ⟨injective_id, Sum.map_injective.mpr ⟨injective_id,Sum.map_injective.mpr ⟨injective_id,Sum.inl_injective⟩⟩⟩⟩ -- need (Y)
lemma pressureLog (K:Grid c→ℝ)(S:St c)(z:ℂ)(U:Grid c): heartS ((talc Y).EvalE z) P.threshold K S U=heartS (Y.EvalE z) P.threshold K S U:=by
     unfold heartS; apply congr_arg; let F:=Y.EvalE z; let G:=(talc Y).EvalE z
     let f:=letters F P.threshold U; let g:=letters G P.threshold U; have hg: f=g ∘ mapV Y :=by funext i; rcases i with i|i|i|i; all_goals rfl
     have he: Function.support g⊆Set.range (mapV Y):=by
         rintro (i|i|i|i|i) hi
         · exact ⟨.inl i,rfl⟩
         · exact ⟨.inr (.inl i),rfl⟩
         · exact ⟨.inr (.inr (.inl i)),rfl⟩
         · exact ⟨.inr (.inr (.inr i)),rfl⟩
         apply False.elim (hi ?_); let j:(ζY).B:= Sum.inr i; unfold g letters; unfold masked Set.indicator; split
         · change z^(ζY).ad j • (0:EvenA c N)=0; rw [smul_zero]
         rfl
     change (∑' i, g i)= (∑' i,f i); rw [hg]; exact ((mapV Y).injective.tsum_eq he).symm
noncomputable def mapK : KIndex Y ↪ KIndex (talc Y):= ⟨Sum.map id (Sum.map Sum.inl id), Sum.map_injective.mpr ⟨ injective_id, Sum.map_injective.mpr ⟨Sum.inl_injective,injective_id⟩⟩⟩
lemma fiscal (hF:1 ≤ fan L η x)(h:Desk Y P b L x η)(hr:P.B=highR L x)(hf:Fare Y P L x η A D)(z:ℂ)(hz:‖z‖≤1): Correspond (Y.EvalK z) ((talc Y).EvalK z):=by
     let F:=Y.EvalK z; let G:= (talc Y).EvalK z
     have hZ:1≤taxK L x 1:=Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le)
     have h1:= ensures F ( (materCost Y hr h hf z hz).bill) hZ (by norm_num) hF -- verify argument order b.P
     have h2:= ensures G ((materCost (talc Y) hr (chalk Y h) (silt Y hf) z hz).bill) hZ (by norm_num) hF
     refine ⟨h1,h2,fun i V=>?_⟩; let g (j: KIndex (ζY)) := if G.addr j=i then G.warp j V else 0
     have hg:support g⊆ Set.range (mapK Y):=by
        rintro (j|(j|j)|j) hi
        · exact ⟨.inl j,rfl⟩
        · exact ⟨.inr (.inl j),rfl⟩
        · apply False.elim (hi ?_); unfold g; split; · change z • (0:EvenA c N)=0; rw [smul_zero]
          rfl
        exact ⟨.inr (.inr j),rfl⟩
     rw [fingerprint,fingerprint]; refine Eq.trans ?_ ((mapK Y).injective.tsum_eq hg); apply tsum_congr; rintro (j|j|j); all_goals rfl
lemma canvass (hF:1 ≤ fan L η x)(h:Desk Y P b L x η)(hr:P.B=highR L x)(hf:Fare Y P L x η A D)(z:ℂ)(hz:‖z‖≤1)(K:Grid c→ℝ)(U:St c): Maternal ζY P K U z= Maternal Y P K U z:=by
      funext V; have hz':= fiscal Y hF h hr hf z hz; unfold Maternal scoreV; rw [pressureLog,goodsK _ _ V (hz'.coins V),goodsK _ _ V (hz'.pays V), funext (fun i=> hz'.governs i V)]
lemma sailB (hF:1 ≤ fan L η x)(h:Desk Y P b L x η)(hr:P.B=highR L x)(hf:Fare Y P L x η A D)(F:ℂ→Pixel c N)(K:Grid c→ℝ)(U:St c)(ht: Library.Wing F Y P x K U): Library.Wing F (talc Y) P x K U:=by obtain ⟨C,h1,h2,h3,h4,h5⟩:=ht.launch; exact ⟨C,h1,h2,h3,h4,fun z hv=> ⟨(h5 z hv).1, (h5 z hv).2.trans (congr_arg (C z • ·) (canvass Y hF h hr hf z hv.le K U).symm)⟩⟩ -- ctor nests? yes.
end Levitate
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.Levitate.sailB
