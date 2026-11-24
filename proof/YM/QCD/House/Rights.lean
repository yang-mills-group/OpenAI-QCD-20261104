import YM.QCD.House.Vow
import YM.QCD.Gas.Verdure

/-! # Forest purchases and wash budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
-- define Live
abbrev shellF (Y:Fleet H ι N) := (Y.suitcase (Classical.choice (Tree.select S.ratio S.patch.odd_side)))
def Given (s:I): Prop:= (Y.fullA s).Nonempty∧ Ac.Spark (Y.shellF).gP s∧(Y.shellF).born s
abbrev celtic (S: StepData c f) (p: Pipe.Clump S ι) := (roster p.toLeft).flags
abbrev Dark (Y:Fleet H ι N):= {s:Pipe.Clump S ι // Given Y s ∧ (roster s.toLeft).flags.Nonempty}
abbrev Bright (Y:Fleet H ι N):= {s:Pipe.Clump S ι // Given Y s ∧ (roster s.toLeft).flags=∅}
-- conditional pointwise F from material
structure Feasible :Prop where
 spark i U V:Y.works i U V ≠ 0→ (Y.ground i).Nonempty

set_option maxHeartbeats 1000000 in
lemma named (X:C' F)(s:I)(h:Y.Feasible)(hx:X.x=τ)(hp: (Y.suitcase F).shootsP X s≠0): Y.Given s:=by
   let Z:=Y.suitcase F
   unfold Pipe.shootsP at hp; split at hp
   next he=>
     refine ⟨?_,he.1, he.2.1⟩
     obtain ⟨u,hu⟩:= he.1.1; rcases u with u|u
     · have heQ: Matter.troupe T R Q.halo (radiusB τ) s.toLeft:= he.2.1.1
       have hQ := Silica.Utopia.lengthP (H:=H) s.toLeft heQ u (mem_toLeft.mpr hu)
       have hp' := Nat.pos_of_ne_zero (n:=coverNumber (radiusB τ) (H.supportP u)) (by omega)
       exact ((Animals.price_pos ..).1 hp').mono (subset_biUnion_of_mem Z.gP hu)
     by_contra hann
     apply hp; unfold draws choiceS; suffices hP:∀ i:S.Choices, call ((Matter.planted X s.toLeft).taggedL i) ((Y.suitcase F).capacityP s (own s.toLeft))=0 by simp_rw [hP]; rw [sum_const_zero,smul_zero]
     intro i; let X':=(planted X s.toLeft).taggedL i
     have hU(A:F.Slice su × Air f su): (Z.capacityP s (own s.toLeft) (X'.wrapY A.1) A.2)=0:=by
        unfold Pipe.capacityP; rw [show Z.averageP s.toRight (X'.wrapY A.1) A.2=0 from ?_,smul_zero]; apply Finset.prod_eq_zero (mem_toRight.mpr hu); let ψ:= X'.wrapY A.1; let U' := ψ.input (ψ.liftA R.beta A.2); have hf:Y.works u U' ψ.V=0:=by_contra fun hh=>hann ((h.spark u U' ψ.V hh).mono (Z.leP s (mem_toRight.mpr hu))); exact congr_arg (Y.riseP ψ A.2 u • ·) hf|>.trans (smul_zero _)
     change call X' (Z.capacityP s (own s.toLeft))=0; unfold call; exact (integral_congr_ae (ae_of_all ((F.order su).prod X'.dice) hU)).trans (integral_zero ..)
   next he=> exact (hp rfl).elim
lemma held_ne (s:I)(V:Grid c)(χ:Chi)(h:Y.Feasible)(hp:Y.vF s χ V≠0): Y.Given s:=by
    by_contra hn; apply hp; let p i:=PhysicalNext.Repeat.Greenbelt.prism T τ χ o.K V (allot i); have hf i:(Y.suitcase (allot i)).shootsP (p i) s=0:=by_contra fun hg=>hn (named Y (p i) s h rfl hg)
    change (Fintype.card (Reserve S):ℝ)⁻¹ •(∑ i,(Y.suitcase _).shootsP (p i) s)=0; simp_rw [hf,sum_const_zero,smul_zero]

def labelF : Y.Dark ⊕ Y.Bright → Pipe.Clump S ι:=Sum.elim Subtype.val Subtype.val
lemma bee : Injective Y.labelF:=by
   rintro (i|i) (j|j) he
   · exact congr_arg _ (Subtype.ext he)
   · exact False.elim (i.2.2.ne_empty ((show i.val=j.val from he).symm ▸ j.2.2))
   · exact False.elim (j.2.2.ne_empty ((show i.val=j.val from he) ▸ i.2.2))
   exact congr_arg _ (Subtype.ext he)

def broad (i:Y.Dark) : Support c := Y.fullA i.val
def invD (i:Y.Dark) : Support c := (roster i.val.toLeft).flags
def lightF (i:Y.Bright): Support c:= Y.fullA i.val
def duskV (χ:Chi)(V:Grid c)(i:Y.Dark): EvenA c N:= Y.vF i.val χ V
def dawnV (χ:Chi)(V:Grid c)(i:Y.Bright):EvenA c N:=Y.vF i.val χ V

def registry (s:Finset (Y.Dark⊕Y.Bright)):Finset (Pipe.Clump S ι):= s.image Y.labelF
lemma call_book (s:Finset (Y.Dark⊕Y.Bright))(χ:Chi)(V:Grid c): Y.emergingF (Y.registry s) χ V= GasP.harvest Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) V) (Y.duskV χ V) (Y.dawnV χ V) s:=by
   have ht : ∀ i∈Y.registry s, Y.Given i:=fun i hi=>by obtain ⟨a,h,rfl⟩:=mem_image.mp hi; cases a <;> next j=> exact j.2.1
   have he : ∀ i: Y.Dark⊕Y.Bright, Y.fullA (Y.labelF i)= Sum.elim Y.broad Y.lightF i:=by rintro (i|i)<;> rfl
   have hg : (Y.okClump (Y.registry s)) ↔ (s:Set (Y.Dark⊕Y.Bright)).PairwiseDisjoint (Sum.elim Y.broad Y.lightF):=by
       refine Iff.intro (fun hv i hi j hj hn=> ?_) (fun hp=> ⟨fun i hi=>(ht _ hi).2.1,?_⟩)
       · change Disjoint (Sum.elim ..) (Sum.elim ..); rw [← he,← he]; exact hv.2 (Finset.mem_image_of_mem Y.labelF (show _ from hi)) (Finset.mem_image_of_mem Y.labelF (show _ from hj)) ((bee Y).ne hn) -- macro
       intro i hi j hj hh; obtain ⟨a,ha,rfl⟩:=mem_image.mp hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hj; change Disjoint (Y.fullA _) (Y.fullA _); rw [he,he]; exact hp ha hb (fun he=>hh (congr_arg _ he))
   have hF : s.toLeft.biUnion Y.invD=(Y.registry s).biUnion (fun i=>(roster i.toLeft).flags):=by
       unfold registry; rw [image_biUnion]; ext y; simp only [mem_biUnion,mem_toLeft]; refine ⟨fun ⟨i,hx,h⟩=>⟨.inl i,hx,h⟩,?_⟩
       rintro ⟨i,hj,h⟩; rcases i with i|i; · exact ⟨i,hj,h⟩
       exact False.elim (by have hp:(roster (toLeft i.val)).flags=∅:= i.2.2; change y∈(roster (toLeft i.val)).flags at h; rw [hp] at h; exact Finset.notMem_empty _ h)
   unfold emergingF GasP.harvest; apply if_congr
   · exact and_congr hg (by rw [hF,Eq.comm])
   · unfold registry; rw [prod_image (Y.bee.injOn)]; exact prod_congr rfl (fun i _=>by rcases i with i|i<;> rfl)
   exact rfl
lemma followup (s:Finset I)(V:Grid c)(χ:Chi)(he:Y.Feasible) (hp:Y.emergingF s χ V≠0): s∈Set.range Y.registry:=by
   unfold emergingF at hp; split at hp
   next ht=>
      let f : Y.Dark⊕Y.Bright → Pipe.Clump S ι:=Y.labelF; let a:=s.preimage f (Y.bee.injOn); refine ⟨a, Finset.ext fun i=>?_⟩
      constructor
      · intro h; obtain ⟨p,hw,rfl⟩:=mem_image.mp h; exact mem_preimage.mp hw
      intro hi; have he': Y.Given i:= held_ne Y i V χ he (fun h=>hp (Finset.prod_eq_zero hi h))
      rcases (roster i.toLeft).flags.eq_empty_or_nonempty with h|h; · exact mem_image.mpr ⟨.inr ⟨i,he',h⟩, mem_preimage.mpr hi,rfl⟩
      exact mem_image.mpr ⟨.inl ⟨i,he',h⟩,mem_preimage.mpr hi,rfl⟩
   next h=> exact (hp rfl).elim
end YM.QCD.Loom.Fleet
