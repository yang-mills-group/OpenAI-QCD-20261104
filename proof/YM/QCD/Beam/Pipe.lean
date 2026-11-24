import YM.QCD.Beam.Heli
/-! # What can be scheduled with a molecule -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{δ β τ μ W C:ℝ} {R:Rep G f}{F:Forest S.ratio}{Q:Target G P}{o :Target.Order G W}
variable {M: Type*} [NormedCommRing M][NormedAlgebra ℝ M][CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M][FiniteDimensional ℝ M]
variable {H:Cash W τ μ L Q o C T R}
variable {ι : Type}
open scoped Classical
structure Pipe (H:Cash W τ μ L Q o C T R)(F: Forest S.ratio)(M: Type*) (ι :Type) where -- no instances here? Prop fields later
 ground : ι→Support c
 limit : ι→Finset ℕ
 compat : ι→ι→Prop
 virtual : ι → StampF F T M
 actual : ι→ Config G f→ Config G c→M

variable (Y:Pipe H F M ι)
-- related compatible predicate imposes only on intersect.
namespace Pipe
def filterP (v:Finset ι): Finset ℕ:= v.biUnion Y.limit
def sweepP (v:Finset ι) (U:Config G c)(x:Config G f) := ∏ i∈v,Y.actual i x U
def averageP (v:Finset ι)(X:Coat T F)(w:Air f G) := ∏ i∈v,Y.virtual i X w
def eligibleP (v:Finset ι):Prop:= (v:Set ι).Pairwise Y.compat
structure Viable :Prop where
 frames :∀ i j,¬Y.compat i j → ¬Disjoint (Y.ground i) (Y.ground j)
 homes :∀ i j (hj:j∈Y.limit i),∀ y : Site f,y∈(R.activities.forced j).support → S.ratio.parent y∈Y.ground i
 pays i : exposedG H (Y.virtual i)
 meets i : silence H (Y.ground i) (Y.virtual i)
 price i V: Envelope fun U=> Y.actual i U V
 allows i V (g:Site f→G.El)(h:∀ i,g (S.ratio.embed i)=1) (U:Config G f):Y.actual i (Lattice.gauge g U) V= Y.actual i U V
 clicks :∀ (X:Coat T F),X.x=τ→ X.width=o.K→X.manifest →∀ (i:ι) (w:Air f G), let p:=X.liftA R.beta w; X.enforce o.a p X.tier≠0 →Y.virtual i X w=Y.actual i (X.input p) X.V

abbrev Piece (S:StepData c f)(ι:Type):=Head S⊕ ι
abbrev Clump (S:StepData c f)(ι:Type):=Finset (Piece S ι)
local notation "D" => Clump S ι
def gP (s:Piece S ι): Support c:=Sum.elim H.supportP Y.ground s
def full (s:D) := s.biUnion Y.gP
def born (v:D):Prop:= Matter.troupe T R Q.halo (radiusB τ) v.toLeft ∧ Y.eligibleP v.toRight ∧ Matter.own v.toLeft=Y.filterP v.toRight
def legal (v:Finset D):Prop:= (∀ i∈v,Ac.Spark Y.gP i) ∧ (v:Set D).PairwiseDisjoint Y.full
lemma lesserP (s:D):H.unionP s.toLeft⊆ Y.full s:=by
   intro y hy; obtain ⟨i,hi,he⟩:= mem_biUnion.mp hy; exact mem_biUnion.mpr ⟨.inl i,mem_toLeft.mp hi,he⟩
lemma leP (s:D){i:ι}(h:i∈s.toRight): Y.ground i⊆ Y.full s:= subset_biUnion_of_mem Y.gP (mem_toRight.mp h)
lemma huesP {v:Finset D}(h:Y.legal v): Ac.Parts Y.gP (v.biUnion id)= v:= Ac.separates _ _ h.1 h.2
lemma diverse {v:Finset D}(h:Y.legal v): (v:Set D).PairwiseDisjoint id:=by have hv := Ac.different Y.gP (v.biUnion id); rwa [huesP Y h] at hv
lemma lefty (v:Finset D): (v.biUnion id).toLeft = v.biUnion Finset.toLeft:= by ext; simp [mem_biUnion]
lemma righty (v:Finset D): (v.biUnion id).toRight=v.biUnion Finset.toRight:=by ext; simp [mem_biUnion]
variable {v: Finset D}
lemma onlyP (s :Finset D) (i): i ∈ own (s.biUnion id).toLeft ↔ ∃ a∈s, i∈ own a.toLeft:=by simp [own,mem_biUnion]
lemma seedP (s:Finset D) (i:Seed S): i∈Packets.seeds S (roster (s.biUnion id).toLeft) ↔ ∃ a ∈s,i∈Packets.seeds S (roster a.toLeft):= by simp only [register,mem_biUnion,mem_toLeft,id_eq]; grind
lemma shadeP {v:Finset D} (hv:Y.legal v){a b:D}(ha:a∈v)(hb:b∈v){i:Site c}(hx:i∈ Y.full a)(hy:i∈Y.full b):a=b:=by_contra fun hh=>Finset.disjoint_left.mp (hv.2 ha hb hh) hx hy
lemma troops {v:Finset D} (hv: Y.legal v): Matter.troupe T R Q.halo (radiusB τ) (v.biUnion id).toLeft ↔ ∀ i∈v,Matter.troupe T R Q.halo (radiusB τ) i.toLeft:=by
   let U: D:= v.biUnion id
   have hm i (hi:i∈v): i.toLeft⊆ U.toLeft:=by unfold U; rw [lefty]; exact subset_biUnion_of_mem _ hi
   have hf i j (hj: j∈(roster (i:D).toLeft).costs): startPos S j⊆Y.full i:=(claim_zoneA R T Q.halo (radiusB τ) i.toLeft _ (inl_mem_disjSum ..|>.2 hj)).trans (lesserP Y i)
   have hk i j (hj:j∈own (i:D).toLeft) x (he: x∈ (R.activities.forced j).support) : S.ratio.parent x∈Y.full i:= lesserP Y i (claim_zoneK R T Q.halo (radiusB τ) i.toLeft j hj he)
   have hh i j (hj:j∈ (i:D).toLeft.toLeft) : j.dome (Q.halo*radiusB τ)⊆Y.full i:= (subset_biUnion_of_mem (H.supportP) (mem_toLeft.mp hj)).trans (lesserP Y i)
   change Matter.troupe T R Q.halo (radiusB τ) U.toLeft ↔ _; constructor
   · rintro ⟨p,hA,hB⟩ i hi
     have h:= Matter.subparts _ _ (hm i hi); have hy:=Matter.subrows _ _ (hm i hi)
     refine ⟨⟨fun j hj=>p.checkpoints j (h hj),p.crews.subset h,register _⟩,fun _ hb _ hc=> hA (hy hb) (hy hc),?_⟩
     intro j hj x hx; obtain ⟨l,hl,hx'⟩:= hB j (hy hj) x hx
     have he: Sum.inl l∈ Packets.seeds S (roster U.toLeft):=inl_mem_disjSum.mpr hl
     obtain ⟨b,hb,he⟩:=(Pipe.seedP v _).1 he; have hg:=inl_mem_disjSum.mp (show Sum.inl l∈Packets.seeds S (roster b.toLeft) from he)
     have hq:= Pipe.shadeP Y hv hb hi (hf b l hg (mem_image_of_mem _ hx')) (hk i j hj x ((R.activities.forced j).inventory_sup hx))
     exact ⟨l,hq ▸ hg,hx'⟩
   intro p; have he : U.toLeft.toLeft= v.biUnion fun i=>i.toLeft.toLeft :=by ext; simp [U,mem_biUnion]
   refine ⟨⟨?_,?_,register _⟩,?_,?_⟩
   · rw [he]; intro i hi; obtain ⟨b,hb,hi⟩:=mem_biUnion.mp hi; exact (p b hb).1.checkpoints i hi
   · rw [he]; intro i hi j hj hn; obtain ⟨a,ha,hi⟩:=mem_biUnion.mp hi; obtain ⟨b,hb,hj⟩:=mem_biUnion.mp hj
     by_cases hk:a=b
     · subst b; exact (p a ha).1.crews hi hj hn
     exact ((hv.2 ha hb hk).mono_left (hh a i hi)).mono_right (hh b j hj)
   · intro i hi j hj he; obtain ⟨a,ha,hi⟩:=(onlyP v _).1 hi; obtain ⟨b,hb,hj⟩:=(onlyP v _).1 hj
     by_cases ht:a=b
     · subst b; exact (p a ha).2.1 hi hj he
     exact Finset.disjoint_left.mpr fun x hx hy=>ht (Y.shadeP hv ha hb (hk a i hi x hx) (hk b j hj x hy))
   intro i hi x hx; obtain ⟨a,ha,hi⟩:=(onlyP v i).1 hi; obtain ⟨j,hj,hx'⟩:= (p a ha).2.2 i hi x hx
   exact ⟨j,inl_mem_disjSum.mp (show Sum.inl j∈ Packets.seeds S (roster U.toLeft) from (Pipe.seedP v _).2 ⟨a,ha,inl_mem_disjSum.mpr hj⟩),hx'⟩
lemma fieldsP (v:Finset D) (j:ℕ): j∈ Y.filterP (v.biUnion id).toRight ↔ ∃ i∈v,j∈Y.filterP i.toRight:=by simp only [filterP,mem_biUnion,mem_toRight,id_eq]; grind
lemma together {v:Finset D} (hc :Y.Viable) (h: Y.legal v): Y.born (v.biUnion id) ↔ ∀ i∈v,Y.born i:=by
  let U:=v.biUnion id; have hm i (hi:i∈v) : (i.toRight:Finset ι)⊆ U.toRight:=by unfold U; rw [righty]; exact subset_biUnion_of_mem _ hi
  have hf i j (hj : j∈Y.filterP i.toRight) : (R.activities.forced j).support.image S.ratio.parent⊆ Y.full i:=by
     obtain ⟨b,hb,hj⟩:= mem_biUnion.mp hj; intro x hx; obtain ⟨y,hy,rfl⟩:=mem_image.mp hx; exact leP Y i hb (hc.homes b j hj y hy)
  have hk i j (hj:j∈own (i:D).toLeft) x (he:x∈(R.activities.forced j).support): S.ratio.parent x∈Y.full i:= lesserP Y i (claim_zoneK R T Q.halo (radiusB τ) i.toLeft j hj he)
  have hx j: (R.activities.forced j).support.Nonempty:= (R.activities.forced j).inventory_ne.mono (R.activities.forced j).inventory_sup
  constructor
  · rintro ⟨hv,p,q⟩ i hi; refine ⟨(Y.troops h).1 hv i hi,p.mono (hm i hi),?_⟩
    ext j; obtain ⟨a,ha⟩:=hx j; constructor
    · intro hj; obtain ⟨b,hb,hj'⟩:=(Y.fieldsP v j).1 (q ▸ (onlyP v j).2 ⟨i,hi,hj⟩)
      exact Y.shadeP h hb hi (hf b j hj' (mem_image_of_mem _ ha)) (hk i j hj a ha) ▸ hj'
    intro hj; obtain ⟨b,hb,hj'⟩:=(onlyP v j).1 (q.symm ▸ (Y.fieldsP v j).2 ⟨i,hi,hj⟩)
    exact Y.shadeP h hb hi (hk b j hj' a ha) (hf i j hj (mem_image_of_mem _ ha)) ▸ hj'
  intro H; refine ⟨(Y.troops h).2 fun i hi=> (H i hi).1,?_,?_⟩
  · unfold eligibleP; rw [righty]; intro i hi j hj hh; obtain ⟨a,ha,hi⟩:=mem_biUnion.mp hi; obtain ⟨b,hb,hj⟩:=mem_biUnion.mp hj
    by_cases he:a=b
    · subst b; exact (H a ha).2.1 hi hj hh
    exact by_contra fun hp=> hc.frames i j hp (((h.2 ha hb he).mono_left (leP Y a hi)).mono_right (leP Y b hj))
  ext j; rw [fieldsP,onlyP]; exact ⟨fun ⟨x,hx,h⟩=> ⟨x,hx,(H x hx).2.2 ▸ h⟩,fun ⟨x,hx,h⟩=> ⟨x,hx,(H x hx).2.2.symm ▸ h⟩⟩
end Pipe
end YM.QCD.Beam
