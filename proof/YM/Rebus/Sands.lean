import YM.Rebus.Shield
import YM.Play.Cause
import YM.Cape.Peace
/-! # Common ownership W. Awakening exact by Brief. Calculus upcoming. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open Play.Camp
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{J K':Patch}{P:Teller su}{β x C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I Z E D:Type}[Fintype I]
variable {N i j n k m l r t M B Q:ℕ}
variable (R: Ratio c f)(p:I→Site f)
local notation "Vh"=> R.parent ∘ p
abbrev heather (p:I→ Site c)(r:ℕ)(X:Finset I): Support c:= Cape.cups p (100*r) X
-- W stencil queries viable. use halo thickness as COST.C real gauge specs. 
local notation "Ax"=> spineP p N (majorT l*Q)
local notation "Aw"=> can p (majorT l*Q)
local notation "W0"=> heather Vh B
local notation "W1"=> Cape.cups Vh (innerT l * B)
local notation "W2"=> Cape.cups p (majorT l * Q)
variable {X Y: Finset I}
variable (hQ:Q≤ 2*B)(hL:20*majorT l≤ R.count.val)(hB:0<B)
lemma thaw (hx:Y⊆X) (l:ℕ)(B:ℕ): halo (30*B) (heather Vh B Y)⊆Cape.cups Vh (innerT l*B) X:=by
   intro i hi; obtain ⟨x,hx',h⟩:=halo_spec.mp hi; obtain ⟨y,hy,h₀⟩:=halo_spec.mp hx'; obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
   exact halo_spec.mpr ⟨_,mem_image_of_mem _ (hx hz),((separation_triangle ..).trans ((Nat.add_le_add h₀ h).trans (by unfold innerT; nlinarith)))⟩
include hQ hL hB
lemma refugeA (u:ℕ)(hu:u≤ 80*B)(x: Finset I): (halo u (Cape.cups p (majorT l*Q) x)).image R.parent ⊆ W0 x:=by
   intro i hi; obtain ⟨i,h,rfl⟩:=mem_image.mp hi; obtain ⟨a,ha,hg⟩:=halo_spec.mp h; rw [Cape.cups_eq] at ha; obtain ⟨z,hz,ha⟩:=mem_biUnion.mp ha
   have hb:= puff R p l B Q hB hQ hL _ (mem_image_of_mem _ (show a∈halo (majorT l*Q) {p z} from ha)); have he:=rowL R (halo_spec.mpr ⟨_,mem_singleton_self _,hg⟩)
   exact halo_spec.mpr ⟨_,mem_image_of_mem Vh hz,((separation_triangle ..).trans ((Nat.add_le_add ((Play.Camp.portion ..).mp hb) he).trans (by omega)))⟩
lemma inspectPath {D:Support f}(he:D⊆Cape.cups p (majorT l*Q) X) (U V:Grid f) (h:∀ i:Bond f,R.parent i.1∈heather (R.parent∘p) B X→ U i=V i): Lattice.Agrees (RG.inspected D) U V:=by
    intro i hi _; refine h _ (refugeA R p hQ hL hB 4 (by omega) X (mem_image_of_mem _ (?_))); exact Corona.halo_mono (le_refl 4) he (Extra.Multi.System.within _ hi)
lemma hardy {D:Support f} (he:D⊆Cape.cups p (majorT l*Q) X) (i:Cell f)(h:¬ Disjoint (touched i) D): R.parent i.1∈ W0 X:=by
    obtain ⟨y,hi,hy⟩:=Finset.not_disjoint_iff.mp h; exact refugeA R p hQ hL hB 2 (by omega) X (mem_image_of_mem _ (halo_spec.mpr ⟨_,he hy,(separation_comm ..).trans_le (Work.E01.sep_touched _ _ hi)⟩))
omit hQ hL hB [Fintype I] in
lemma biDU {A₀:Type}{S:I→ Finset A₀}{i:A₀}: i∈ (@Finset.biUnion _ _ (fun a b=>Classical.propDecidable (a=b)) X S) ↔ ∃ a∈ X,i∈ S a := Finset.mem_biUnion
lemma gaugeFt (x: Finset I)(i:Kh f)(h:i∈@Finset.biUnion _ _ (fun a b => Classical.propDecidable (a=b)) x Aw): (RG.touched (Fruit.bleep i)).image R.parent⊆heather (R.parent∘p) B x:=by
    apply Finset.Subset.trans (image_subset_image (show RG.touched _ ⊆ halo 2 (Cape.cups p (majorT l*Q) x) from ?_)) (refugeA R p hQ hL hB 2 (by omega) x); obtain ⟨y,hx,hj⟩:=biDU.mp h; intro j hj'; exact halo_spec.mpr ⟨(Fruit.bleep i).1,by rw [Cape.cups_eq]; exact mem_biUnion.mpr ⟨_,hx,(mem_filter.mp hj).2⟩, Work.E01.sep_touched _ _ hj'⟩ -- line syntax
lemma spinFt (x: Finset I)(i:Keys f N)(h: Sum.inl i∈ @Finset.biUnion _ _ (fun a b => Classical.propDecidable (a=b)) x (spineP p N (majorT l*Q))): (halo B ({locationP i}:Support f)).image R.parent⊆ heather (R.parent∘p) B x:=by
   obtain ⟨y,hx,hy⟩:=biDU.mp h
   refine (image_subset_image (?_)).trans (refugeA R p hQ hL hB B (by omega) _); apply Corona.halo_mono le_rfl; apply singleton_subset_iff.mpr; rw [Cape.cups_eq]; exact mem_biUnion.mpr ⟨_,hx,(mem_filter.mp (inl_mem_disjSum.mp hy)).2⟩
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.gaugeFt
#print axioms YM.MassiveQCD.Rebus.inspectPath
