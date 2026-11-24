import YM.MassiveQCD.Apron.Groves
import YM.Mills.GlueQ
import YM.Play.Needle
/-! # primary mark pinching through regular pay forest. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (M:Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "M'"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
local notation "Β"=>banknote N z' a
variable (Y:Fleet H κ (ample N I))
local notation "Ξ"=> closet H G M X z a
local notation "Tx"=> united (Ξ) Y
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ M)
namespace Camp
open TabletV
variable (p: Finset (Fj D E J))
local notation "V'"=> Wound M
local notation "P'"=> Piece S (Wound M ⊕ κ)
local notation "p'"=> plume P₀ G M p
-- singleton tag on horoscope
def badge (M:Fj D E J→Support c)(S:StepData c f)(κ:Type)(i: Wound M):Clump S (Wound M⊕κ):={Sum.inr (Sum.inl i)}
lemma badgeInj : Injective (badge M S κ) := fun i j he=> Sum.inl_injective (Sum.inr_injective (Finset.singleton_injective he))
lemma partV (i:V'): (Tx).fullA (badge M S κ i)=i.val.biUnion M:=by
   let A:P':=Sum.inr (Sum.inl i); change (Tx).shellF.full {A}= _; rw [Pipe.full,singleton_biUnion]; rfl
-- singleton only by compatibility.
lemma offspring (s:Finset P') (hs:(Tx).Given s) (hp:∀ i∈s,∃ j:V',i=Sum.inr (Sum.inl j)) :∃ j:V',s=badge M S κ j:=by
   have hx := hs.2.1; obtain ⟨i,hi⟩:=hx.1
   have hv (j k) (he:Ac.bonds (Tx).shellF.gP s j k): j=k:=by
      obtain ⟨hj,hk,x,hx,hy⟩:=he
      obtain ⟨v,rfl⟩:=hp j hj; obtain ⟨w,rfl⟩:=hp k hk; by_contra hn
      have hz : Disjoint (v.val.biUnion M) (w.val.biUnion M):= hs.2.2.2.1 (mem_toRight.mpr hj) (mem_toRight.mpr hk) (fun h=>hn (congr_arg _ h))
      exact Finset.disjoint_left.mp hz hx hy
   have hk (j) (h:Ac.chain (Tx).shellF.gP s i j): i=j:=by induction h with
     | refl=> rfl
     | tail _ he ih=> exact ih.trans (hv _ _ he)
   obtain ⟨k,rfl⟩:=hp i hi; refine ⟨k, Finset.eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj=> (hk _ (hx.2 _ hi _ hj)).symm⟩⟩
private lemma lightP (i:V')(he:spent i.val=∅)(hh:(i.val.biUnion M).Nonempty): Given (Tx) (badge M S κ i)∧ (roster ((badge M S κ i).toLeft)).flags=∅:=by
   let Gx:=Tx; let s:=badge M S κ i; have hv : s.toLeft=∅:=by ext; simp [s,badge]
   have hx : s.toRight={Sum.inl i}:=by ext; simp [s,badge]
   have hF: Gx.shellF.born s:=by
      unfold Pipe.born; rw [hv,hx]
      have hV: own (∅:Finset (Head S))=∅:=by ext; simp [Matter.own]
      refine ⟨?_,by unfold eligibleP; rw [coe_singleton]; exact Set.pairwise_singleton .., ?_⟩
      · unfold troupe; rw [hV]; let A:= roster (∅:Finset (Head S)); refine ⟨⟨?_,?_,register _⟩,?_,?_⟩
        · intro i hi; simp at hi
        · intro i hi; simp at hi
        · intro i hi; simp at hi
        · intro i hi; simp at hi
      rw [filterP,singleton_biUnion,hV]; change _=typo (P₀.wish (spent i.val)); simp only [he,Rise.wish,biUnion_empty]; ext; simp [typo] -- inspect
   refine ⟨⟨(partV H G M X z a Y i).symm ▸ hh,⟨singleton_nonempty _,fun j hj k hk=>?_⟩,hF⟩,?_⟩ -- G shadow
   · rw [mem_singleton.mp (show j∈{Sum.inr (Sum.inl i)} from hj),mem_singleton.mp (show k∈{Sum.inr (Sum.inl i)} from hk)]; exact .refl
   rw [show _=s.toLeft from rfl,hv]; ext; simp [roster,Packets.store]
set_option quotPrecheck false
variable (hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)
local notation "Ip"=> ↥(plume P₀ G M p)
def child (i:Ip) : V':= ⟨i.val,(mem_filter.mp i.2).2.1⟩
lemma childInj : Injective (child (P₀:=P₀) G M p) :=fun _ _ he=>Subtype.ext ((show _ from congr_arg (fun x:V'=>x.val) he))
include hw hk hs he
def student (hk:Cove.Count G P₀ M)(hw:X.Wave O.threshold q' z)(hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)(i:Ip):(Tx).Bright:=⟨badge M S κ (child G M p i),by
   have hv:= mem_powerset.mp (mem_filter.mp i.2).1; have he':=spentP _ _ hv he; obtain ⟨a,ha⟩:=lush (P:=P₀) G i.val ((child G M p i).2.1) he' (mem_filter.mp i.2).2.2
   refine lightP H G M X z _ Y _ he' ?_; obtain ⟨b,hb⟩:= hs a (mem_toLeft.mpr (mem_toRight.mpr (hv (mem_toRight.mp (mem_toLeft.mp ha)))))
   exact ⟨_, X.endowment G hw hk i.val (mem_image_of_mem _ (mem_union_left _ (mem_biUnion.mpr ⟨a,ha,hb⟩)))⟩⟩
-- `include` pollution inspect
local notation "H'"=> student H G M X z a Y p hk hw hs he
lemma pupil : Injective H' := fun _ _ he=> childInj G M p (badgeInj M (congr_arg Subtype.val he))
-- rainbow on s reduced horoscopes. Space equality
/-- all forest cones for a given highest tuple restriction. -/
abbrev campus (hk:Cove.Count G P₀ M)(hw:X.Wave O.threshold q' z)(hs:∀ j∈ leftE p, (X.spine j).Nonempty)(he:spent p=∅) : Finset (Tx).Bright := univ.image (student H G M X z a Y p hk hw hs he)
def month (M:Fj D E J→Support c)(G:Send S.ratio N D)(p:Finset (Fj D E J)): Finset (Finset ↥(TabletV.plume P₀ G M p)):= univ.filter fun (s:Finset ↥(TabletV.plume P₀ G M p))=> (s:Set _).PairwiseDisjoint (fun i:↥(TabletV.plume P₀ G M p)=>i.val.biUnion M)
local notation "Z"=> campus H G M X z a Y p hk hw hs he
open GasP
abbrev cliques {ι:Type}(u:ι→Support c)(W:Finset ι): Finset (Finset ι):= W.powerset.filter fun (s:Finset ι)=>(s:Set ι).PairwiseDisjoint u
lemma clinics : cliques (Tx).lightF Z=(month (P₀:=P₀) M G p).image (fun s=>s.image H'):=by
    let B:= H'; let L:=(Tx).lightF
    have hψ (i:Ip) : L (B i)= i.val.biUnion M:= partV H G M X z a Y _
    have hu :=pupil H G M X z a Y hw hk p hs he -- order
    ext s; constructor
    · intro hp; obtain ⟨hv,hQ⟩:=mem_filter.mp hp; have he':=mem_powerset.mp hv; let t':Finset Ip:=s.preimage B hu.injOn
      refine mem_image.mpr ⟨t',mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
      · intro i hi j hj hh; change Disjoint (i.val.biUnion M) (j.val.biUnion M); rw [← hψ,←hψ]; exact hQ (mem_preimage.mp hi) (mem_preimage.mp hj) (hu.ne hh)
      change t'.image B=s; ext i; constructor; · intro hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hi; exact mem_preimage.mp hb
      intro hi; obtain ⟨v,-,hv⟩:=mem_image.mp (he' hi); exact mem_image.mpr ⟨v,mem_preimage.mpr (show B v ∈ s from (show B v=i from hv).symm ▸ hi),hv⟩
    intro hv; obtain ⟨u,hu',rfl⟩:=mem_image.mp hv; refine mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (subset_univ _)),?_⟩; intro i hi j hj hh; obtain ⟨b,hb,rfl⟩:=mem_image.mp hi; obtain ⟨c,hc,rfl⟩:=mem_image.mp hj; change Disjoint (L (B b)) (L (B c)); rw [hψ,hψ]; exact (mem_filter.mp hu').2 hb hc (fun h=>hh (congr_arg _ h))
omit hw hk hs he
lemma symphony : chest P₀ G M p=(month (P₀:=P₀) M G p).image (fun s=>s.image Subtype.val):=by
    ext s; let B(i:Ip):=i.val; have hB : Injective B:=Subtype.val_injective; constructor
    · intro hp; obtain ⟨hv,hQ⟩:=mem_filter.mp hp; have he':=mem_powerset.mp hv; let u:=s.preimage B hB.injOn; refine mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,fun i hi j hj hh=>hQ (mem_preimage.mp hi) (mem_preimage.mp hj) (hB.ne hh)⟩,?_⟩; ext i; constructor
      · intro hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hi; exact mem_preimage.mp hb
      intro hi; exact mem_image.mpr ⟨⟨i,he' hi⟩,mem_preimage.mpr hi,rfl⟩
    intro hv; obtain ⟨u,hu,rfl⟩:=mem_image.mp hv; refine mem_filter.mpr ⟨mem_powerset.mpr (fun i hi=>by obtain ⟨b,hb,rfl⟩:=mem_image.mp hi; exact b.property),?_⟩; intro i hi j hj hh; obtain ⟨b,hb,rfl⟩:=mem_image.mp hi; obtain ⟨c,hc,rfl⟩:=mem_image.mp hj; exact (mem_filter.mp hu).2 hb hc (fun h=> hh (congr_arg _ h))
end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.symphony
#print axioms YM.MassiveQCD.Play.Camp.clinics
