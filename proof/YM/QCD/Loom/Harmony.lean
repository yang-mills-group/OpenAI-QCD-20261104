import YM.QCD.Loom.Nap
import YM.QCD.Jets.Guide
/-! # Fleet for HUE gas from core Expansion -- generic S on correct ratio -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R : BudgetPoint}
variable {H:Cash W τ μ L Q o C T (trimP T R δ β b)}{ι D E K:Type}{N:ℕ}

local notation "Ξ" => Fj D E K
-- choose large roofM, with space for enforce buffers
abbrev Wound (X:Ξ → Support c):= {i: Finset (Fj D E K) // spark X i}
variable (Y:Send S.ratio N D)(p:Rise f N E K)(X:Fj D E K→Support c)
lemma montane (t: Finset (Fj D E K)): RG.inspected (brimW Y p t)= t.biUnion fun i=> RG.inspected (brim Y p i):=by
   unfold RG.inspected brimW; ext x; simp only [mem_union,mem_biUnion, mem_univ,true_and]; constructor
   · rintro (⟨j,hj,hx⟩|⟨k,hk⟩)
     · exact ⟨j,hj,Or.inl hx⟩
     split at hk
     next he=> simp only [notMem_empty] at hk
     next he=> obtain ⟨i,hv,he⟩:= Finset.not_disjoint_iff.mp he; obtain ⟨j,hj,hv⟩:= mem_biUnion.mp hv; exact ⟨j,hj,Or.inr ⟨k,by rw [if_neg (Finset.not_disjoint_iff.mpr ⟨_,hv,he⟩)]; exact hk⟩⟩
   rintro ⟨j,hj,hx|⟨k,hx⟩⟩
   · exact Or.inl ⟨_,hj,hx⟩
   refine Or.inr ⟨k,?_⟩; split at hx
   next he=> simp only [notMem_empty] at hx
   next he=> obtain ⟨x,hx',ht⟩:= Finset.not_disjoint_iff.mp he; rw [if_neg (Finset.not_disjoint_iff.mpr ⟨_,mem_biUnion.mpr ⟨j,hj,hx'⟩,ht⟩)]; exact hx

def petal (t: Finset Ξ): Support f:=RG.inspected (brimW Y p t)
def radio (i: Finset Ξ): Support c:= (petal Y p i).image S.ratio.parent
def budget (v: Finset Ξ):= (p.wish (spent v)).card
lemma planet (t:Finset Ξ): halo (30*radiusB τ) (radio Y p t) ⊆ t.biUnion (roof Y p 30 (radiusB τ)) :=by
    intro i hi; obtain ⟨u,hu,hx⟩:= halo_spec.mp hi; obtain ⟨x,hx',rfl⟩:=mem_image.mp hu; rw [petal,montane] at hx'; obtain ⟨a,ha,hx'⟩:=mem_biUnion.mp hx'; exact mem_biUnion.mpr ⟨a,ha,halo_spec.mpr ⟨_,mem_image_of_mem _ hx',hx⟩⟩
variable (H)
variable [Fintype D][Countable E][Countable K]
local notation "A" => Wound X
local notation "t"=>R.threshold
-- separate δ inverse even operator.
def deckHue : Fleet H (Wound X) N where
 limit i:= typo (p.wish (spent i.1))
 ground i:= i.1.biUnion X
 fine i:= petal Y p i.1
 window i:= radio Y p i.1
 compat i j:= Disjoint (i.1.biUnion X) (j.1.biUnion X)
 works i U _ := δ⁻¹ ^ budget p i.1 • hue Y p t i.1 U
instance (X:Fj D E K→ Support c):Countable (Wound X):=by unfold Wound; infer_instance
variable {m : D→ℝ} {q : E→ℝ}{e : K→ℝ} {w h v z:ℝ}
lemma rigid {f1: Grid f→EvenA c N}(hb: Measurable (Cove.light (Keys c N) ∘ f1)) : Measurable f1:= (Measurable.subtype_mk (p:=fun x:Grass.Alg _=> x∈ roomA (Keys c N)) (f:=fun i=> (f1 i).val) hb)
lemma tore (s:EvenA c N)(he:1≤v): ‖s‖ ≤‖token c N v s‖:=by
   rw [pulse,dry _ (fun _=> zero_lt_one.trans_le he)]; change ‖light _ s‖≤ _; rw [Grass.norm_def]; refine Finset.sum_le_sum (fun i _=> ?_); exact le_mul_of_one_le_left (norm_nonneg _) (Finset.one_le_prod (fun a _=> he))
include H
lemma homeP (hz : Peak Y t h v w m) (hm : Cents p q e h t)(hp:p.Wave t)(hd:0<δ)
    (he : X= roof Y p 30 (radiusB τ))(hv:1≤v)
    (hh:∀ (U:Grid f)(g:Lat.Frame f),(∀ i,g (S.ratio.embed i)=1) →∀ s, hue Y p t s (Lattice.gauge g U)=hue Y p t s U) : (deckHue H Y p X).Famous :=by
   let G:= deckHue H Y p X; have hg (i:Wound X): halo (30*radiusB τ) (radio Y p i.1)⊆ i.1.biUnion X:=by
      exact ((fun hb=> Eq.subst (motive:=fun g=> halo (30*radiusB τ) (radio Y p i.1)⊆ i.1.biUnion g) he.symm hb) (planet Y p i.1)) -- X transport issues
   refine ⟨fun i=>Subset.refl _,hg,?_,fun _ _ _ _ _=>rfl,?_,?_,fun _ _ p=>p,?_⟩
   · exact fun i _ U V h=> congr_arg (δ⁻¹ ^ budget p i.1 • ·) (RG.UsesFinal.allReads t _ _ (stillL Y p t hp _) U V h)
   · intro i V; obtain ⟨a,ha⟩:=i
     let κ:= hue Y p t a
     have he : Envelope κ:= ⟨rigid (morals Y p t hp a),_,fun x=> (tore _ hv).trans (pinches Y p hz hm hp x ha)⟩
     exact Env.scale (Envelope.const (δ⁻¹ ^ budget p a)) he
   · intro i V g he U; exact congr_arg (δ⁻¹ ^ budget p i.1 • ·) (hh U g he i.1)
   intro i j he x hx; obtain ⟨y,hy,rfl⟩:=mem_image.mp he; change x∈ ({YM.PhysicalNext.Repeat.Pane.abscissas f (mac y)}: Support f) at hx
   rw [comes,mem_singleton] at hx; subst x; refine hg i (halo_subset _ _ ?_); have hv := Cove.native_sub Y p i.1 (Cove.wish_sub Y p i.1 hy)
   exact mem_image_of_mem _ (mem_union_left _ hv)
open Sway OrbitG Flume Grass Lat YM.Next.Free
lemma outfit (hp:p.Reframe)(U:Grid f)(g:Lat.Frame f): Parade (Lattice.gauge g U) U (trade (rotates N g)) p (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t :=by
   refine ⟨by simp,fun _=>Finset.image_id.symm,fun _=>rfl,fun _=> Finset.image_id.symm,fun _=>Finset.image_id.symm, fun i=> Subtype.ext ?_,fun i=>Subtype.ext ?_⟩
   · exact hp.main i U g
   exact hp.plug i U g
lemma flower (s: Lat.Frame c)(he: s=fun _=>1)(a:EvenA c N): (trade (rotates N s)).passL a=a:=by
   subst s
   apply Subtype.ext; change Lat.slots N (fun _=>1) a.val= a.val
   have hm:rotates N (fun _:Site c=>1)=1:=by
      unfold Lat.rotates; rw [show siteRot (fun _:Site c=>1)=1 from ?_,copies_one]
      unfold siteRot; simp_rw [show colour 1=1 from rfl,Lat.touch_one]; exact Lat.ridden
   unfold Lat.slots; rw [hm,star_one, Matrix.transpose_one];
   exact Grass.adapt_one ..
lemma fowl {j k :ℕ}{h' C₁:ℝ}(L₁: Flight j k)(L':f.val=c.val*L₁.L.val){d: Grid f→Sheet f} {hx:ℕ} (Q: Sun L₁ c f L' h h' v w C₁ hx d)(u:Grid f)(g: Lat.Frame f)(he:∀ i,g ((sliceL L₁ L').embed i)=1)(b:ℕ)(hp:p.Reframe) (s):
       hue (Q.equip N b) p t s (Lattice.gauge g u)=hue (Q.equip N b) p t s u:=by
    have hh:= Sway.heatE Q N b u g; have ht:= Sway.hatch hh (outfit H p hp u g) s
    have he': g ∘ (sliceL L₁ L').embed=fun _=>1 := funext he
    have hr:=flower (N:=N) H (g ∘ (sliceL L₁ L').embed) he'
    refine Eq.trans (hr _).symm (ht.trans ?_); congr 1; simp [Sway.sail]
end YM.QCD.Loom
