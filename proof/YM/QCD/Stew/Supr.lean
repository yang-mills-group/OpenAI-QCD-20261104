import YM.QCD.Stew.Julian
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quotes
/-! # New projected support stencils sans scalar path. Emits liens on truly unmasked fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u t:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port
variable {ι:Type}(E:Gem c N ι)(b:Flavor N)
open Residual
-- mode A. full support includes single-link stencil reach. no withering on other links.
def way (b:RegularAddress c):Support c:= b.support ∪ stand b.site
def rose (b: RegularAddress c): RegularAddress c:=⟨b.site, way b,mem_union_left _ b.anchor⟩
lemma skyRose (b:RegularAddress c)(v:Strut c): rose (rotateL b v)=rotateL (rose b) v:=by
    have he:way (rotateL b v)=(way b).image (act v):=by
       unfold way; rw [image_union]; congr 1
       change stand (act v _)= (stand b.site).image (act v); unfold stand; rw [← image_singleton, halo_map (act v) (turn_sep v.1 v.2)] -- sig
    unfold rose rotateL; congr 1

def dearth : Gem c N ι:= ⟨rose ∘ E.addr,fun i V=> E.view i V-mintF E b V i⟩
lemma lunar (h:E.Gather)(hp:Crossing E): Crossing (dearth E b):=by
   constructor
   · refine ⟨fun i U k=> ?_,fun i U=> ?_,fun i U=> ?_⟩
     · change Lat.slots N k (light _ (_-_))=light _ (_-_); simp only [map_sub]; exact congr_arg₂ _ (hp.blank.gauge i U k) (gainR E b i U k)
     · intro W h; change sways _ (_-_)=_; rw [map_sub]; refine congr_arg₂ _ (hp.blank.num i U W h) ?_; exact form_fit _ N W h
     change Regal c N (_-_)=_; rw [map_sub]; exact congr_arg₂ _ (hp.blank.real i U) (warpR E b hp.blank i U)
   intro p k g hh; obtain ⟨v,hv⟩:= hp.rays _ _ _ hh
   refine ⟨v,fun i=>?_⟩; have hk:=hv i; have ht: rose (E.addr (v i))=rotateL (rose (E.addr i)) p:=by rw [hk.1, skyRose]
   refine ⟨ht,fun V=>?_⟩; change Diode _ _ _ _ (_- _)=_; rw [map_sub, hk.2,turnC E b p k g hh i _ hk.1 hk.2 (h.role ..) (hp.blank.num i 1) (hp.blank.gauge _)] -- edit
   rfl
def Quanta (E:Gem c N ι)(b:Flavor N):Prop:=∀ i,Nonwrapping (E.addr i).support (E.addr i).site → ∀ j,shape (E.addr i).site (feeF b (E.view i 1)) j=0
lemma emptyRide (h:4 ≤ c.val): Quanta (dearth E b) b:=by
    intro i hn j; let o:= (E.addr i).site
    have hp : Nonwrapping (E.addr i).support o:=fun j hh=> hn j (mem_union_left _ hh)
    change (profile o j) ((meter b) (E.view i 1- _))=0; rw [map_sub,map_sub]; change _-shape o (feeF b (mintF E b 1 i)) j=0; rw [addressT E b h i j]; unfold lane mote; rw [if_pos hp]; exact sub_self _
noncomputable def lien (t:ℝ): Ruby.Hue c N ι := ⟨fun i=>way (E.addr i), fun i V=>letters E t V i- (letters (dearth E b) t V i+mintF E b V i)⟩
lemma clearUse (i:ι)(hV:LocalOn (E.addr i).support (E.view i)) (t:ℝ) : UsesFinal t (E.addr i).support (fun V=>letters E t V i):=by
    intro U V he ht; have hh:Healthy t (E.addr i).support U↔ Healthy t (E.addr i).support V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,ht,← Finset.disjoint_iff_inter_eq_empty];
    by_cases hn: Healthy t (E.addr i).support U
    · exact (masked_eq _ _ _ _ hn).trans ((hV _ _ he).trans (masked_eq _ _ _ _ (hh.1 hn)).symm)
    exact (masked_ne _ _ _ _ hn).trans (masked_ne _ _ _ _ (mt hh.mpr hn)).symm
lemma wingsZ (B: Finset (Site c))(X Y:EvenA c N)(h:Gated B X)(hp:Gated B Y): Gated B (X-Y):=by unfold Gated; rw [map_sub]; exact Subalgebra.sub_mem _ h hp
lemma licit (E: Gem c N ι)(h:E.Gather)(i:ι)(U: Grid c): Gated (E.addr i).support (letters E t U i):=by
    unfold letters; by_cases ht:Healthy t (E.addr i).support U; · rw [masked_eq _ _ _ _ ht]; exact h.role i U
    rw [masked_ne _ _ _ _ ht]; exact Fleet.spruce _
lemma dry (V:Grid c)(i:ι): (lien E b t).mean i V=if Healthy t (way (E.addr i)) V then 0 else letters E t V i-mintF E b V i:=by
    split
    next hv=>
       have hp: Healthy t (E.addr i).support V:= hv.mono_left subset_union_left; change letters E t V i-(masked t (way (E.addr i)) _ V + mintF E b V i)=_; rw [letters,masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hv]
       change _- (E.view i V- _+_)=_; abel
    next hp=> change letters E t V i-(masked _ (way (E.addr i)) _ _+_)= _; rw [masked_ne _ _ _ _ hp,zero_add]
lemma dues (v:ℝ)(h:E.Gather) (hp:(dearth E b).Gather) (hx: (∀ i,Measurable (fun V=>mintF E b V i)))(hk:(∀ i, LocalOn (stand (E.addr i).site) (fun V=>mintF E b V i)))(hG:∀ i U,Gated (stand (E.addr i).site) (mintF E b U i)): (lien E b v).Tall v:=by
    constructor
    · intro i V U hV hU; refine congr_arg₂ (·-·) (Work.H03.reads_larger (show (E.addr i).support⊆ way _ from subset_union_left) (clearUse E i (h.sees i) v) V U hV hU) (congr_arg₂ (·+·) (clearUse (dearth E b) i (hp.sees i) v V U hV hU) ((hk i) V U (agrees_mono hV (Finset.coe_subset.mpr Finset.subset_union_right))))
    · intro i; exact (RG.masked_measurable _ _ _ (h.reads i)).sub ((RG.masked_measurable _ _ _ (hp.reads i)).add (hx i))
    · intro i U he hv; change Healthy v (way (E.addr i)) U at hv; rw [Stew.dry,if_pos hv] at he; exact he rfl
    intro i U; rw [Stew.dry]; split; exact Fleet.spruce _; exact wingsZ _ _ _ (gateMon _ _ subset_union_left _ (licit _ h ..)) (gateMon _ _ subset_union_right _ (hG i U))
end YM.QCD.Stew
