import YM.QCD.Beam.Pipe
/-! # Joint component protocol. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam.Pipe
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{δ β τ μ W C:ℝ} {R:Rep G f}{F:Forest S.ratio}{Q:Target G P}{o :Target.Order G W}
variable {M: Type*} [NormedCommRing M][NormedAlgebra ℝ M][CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M][FiniteDimensional ℝ M]
variable {H:Cash W τ μ L Q o C T R}{ι:Type}
local notation "D" => Clump S ι
variable (Y:Pipe H F M ι)
def capacityP (v:D) (k:Finset ℕ)(X:Coat T F)(w:Air f G):M:= X.term R Q.table W o.a k Q.halo w v.toLeft • Y.averageP v.toRight X w
def shootsP (X:Coat T F) (v:D): M:= if Ac.Spark Y.gP v ∧ Y.born v ∧ RG.flags (Pressure.temp X.x) X.V ∩ Y.full v=(roster v.toLeft).flags then draws (Matter.planted X v.toLeft) (Y.capacityP v (own v.toLeft)) else 0
def drawP (X:Coat T F)(v: Finset D) := if Y.legal v∧ RG.flags (Pressure.temp X.x) X.V= v.biUnion (fun i=>(roster i.toLeft).flags) then ∏ i∈v,Y.shootsP X i else 0
def heldP (X:Coat T F)(s:D):M:= if Y.born s∧ (preps X (roster s.toLeft)).manifest then draws (preps X (roster s.toLeft)) (Y.capacityP s (own s.toLeft)) else 0
lemma ripeP (k:Finset ℕ)(s:D)(h:Y.Viable): exposedG H (Y.capacityP s k):=by
   intro X he hk hv; let f₀:= X.body R Q.table W o.a k Q.halo s.toLeft
   have hp:= H.laws
   have hE:Envelope f₀:= ⟨X.body_b Q.table_exists (he.symm ▸ hp.intake) (by rw [hk,he]; exact H.laws.data.access) ..,_,fun z=> H.every X he hk hv k s.toLeft z.1 z.2⟩
   exact Env.scale hE (envCasting s.toRight (fun j (i:F.Slice G × Air f G)=> Y.virtual j (X.wrapY i.1) i.2) (fun i _=> h.pays i X he hk hv))
lemma habitat (k k':Finset ℕ)(s:D)(h:Y.Viable)(X X':Coat T F)(v v':Air f G)(he:X.x=τ)(hv: Borough X X' (Y.full s) v v' k k' R): Y.capacityP s k X v=Y.capacityP s k' X' v':=by
   unfold capacityP; refine congr_arg₂ (· • ·) (Cash.concord H s.toLeft X X' hv he (Y.lesserP s)) (Finset.prod_congr rfl fun j hj=>h.meets j X X' v v' he ?_ ?_)
   · have hh:=Y.leP s hj; exact ⟨hv.weather,hv.width,hv.chi,fun _ hi=>hv.places _ (hh hi),fun i hi=>hv.frames i (hh hi),fun _ hi=>hv.site _ (hh hi),fun _ hi=>hv.bond _ (hh hi), agrees_mono hv.actual hh⟩
   exact (observe _).2 fun p hp=> hv.airs p (mem_filter.mpr ⟨mem_univ _,fun i hi=> Y.leP s hj ((mem_filter.mp hp).2 _ hi)⟩)
lemma lullP (k:Finset ℕ)(s:D)(h:Y.Viable):silence H (Y.full s) (Y.capacityP s k):=fun X X' v v' he hv hh=>Y.habitat k k s h X X' v v' he ⟨hv,(observe _).1 hh,fun _ _=>Iff.rfl⟩
lemma threadsP (X:Coat T F)(w: Air f G)(k:Finset ℕ)(v:Finset D)(h:Y.legal v):
    Y.capacityP (v.biUnion id) k X w=∏ i∈v,Y.capacityP i k X w:=by
   have hx:=Y.diverse h
   have ha: (v:Set D).PairwiseDisjoint Finset.toLeft:= fun i hi j hj hn=> Finset.disjoint_left.mpr fun a h h'=> Finset.disjoint_left.mp (hx hi hj hn) (mem_toLeft.mp h) (mem_toLeft.mp h')
   have hb: (v:Set D).PairwiseDisjoint Finset.toRight:= fun i hi j hj hn=> Finset.disjoint_left.mpr fun a h h'=> Finset.disjoint_left.mp (hx hi hj hn) (mem_toRight.mp h) (mem_toRight.mp h')
   unfold capacityP averageP Coat.term; rw [lefty,righty,Finset.prod_biUnion ha,Finset.prod_biUnion hb];
   simp only [← Finset.prod_coe_sort v]; exact Eq.symm <| prodSaddle ..
lemma transmitted (X:Coat T F)(k:Finset ℕ)(h:Y.Viable)(v:Finset D)(hp: Y.legal v)(he:X.x=τ)(hk:X.width=o.K)(hX:X.manifest): draws X (Y.capacityP (v.biUnion id) k)= ∏ i∈v,draws X (Y.capacityP i k):=by
   rw [← prod_coe_sort v]; let p i:=draws X (Y.capacityP i k); let h w:=Y.capacityP w k -- rename
   have hv : (↑(univ:Finset (↥v)):Set (↥v)).PairwiseDisjoint (fun i=>Y.full i.val):=fun i _ j _ h=> hp.2 i.2 j.2 (fun he=> h (Subtype.ext he))
   have hm: Y.capacityP (v.biUnion id) k= fun X w=>∏ i:↥v,Y.capacityP i.val k X w:=by funext; rw [Y.threadsP _ _ k v hp,← prod_coe_sort v]
   rw [hm]; exact products H _ (fun i: ↥v=> Y.capacityP i.val k) X he hk hX (fun i=>ripeP Y k i.val ‹_›) (fun i=>lullP Y k i.val ‹_›) hv -- h shadow error
lemma portm (v:Finset D)(x:Site c): x∈(roster (v.biUnion id).toLeft).place↔∃ i∈v,x∈(roster i.toLeft).place:=by
   simp_rw [← Packets.place_reads]; simp only [mem_biUnion];
   have hx:= Pipe.seedP v; grind
lemma swornP (v:Finset D): (roster (v.biUnion id).toLeft).flags=v.biUnion (fun i=> (roster i.toLeft).flags):=by
   ext x; simpa only [mem_biUnion,Packets.seeds,inr_mem_disjSum] using seedP v (Sum.inr (Sum.inr x))
lemma shackledP (h:Y.Viable)(X:Coat T F)(he:X.x=τ)(hk:X.width=o.K)(v:Finset D)(hp:Y.legal v): Y.heldP X (v.biUnion id)=Y.drawP X v:=by
   let U:=v.biUnion id
   let A:= preps X (roster U.toLeft); let B:= RG.flags (Pressure.temp X.x) X.V
   have hL : A.manifest ↔ B=v.biUnion fun i=> (roster i.toLeft).flags:= by unfold manifest A preps U; dsimp only; rw [swornP]; exact eq_comm
   unfold Pipe.heldP Pipe.drawP
   by_cases Hx:A.manifest
   · have hY:=hL.mp Hx; rw [if_pos (show Y.legal v ∧ RG.flags (Pressure.temp X.x) X.V= _ from And.intro hp hY)]
     have hA i (hi:i∈v): RG.flags (Pressure.temp X.x) X.V ∩Y.full i=(roster i.toLeft).flags:=by
        change B ∩_= _; rw [hY]; ext j; constructor
        · intro h; obtain ⟨hf,hb⟩:=mem_inter.mp h; obtain ⟨z,hz,hf⟩:=mem_biUnion.mp hf; exact Y.shadeP hp hz hi (Y.lesserP z (Matter.range_flags (R:=R) (T:=T) (l:=Q.halo) (b:=radiusB τ) _ hf)) hb ▸ hf
        exact fun h=>mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,hi,h⟩,Y.lesserP i (Matter.range_flags (R:=R) (T:=T) (l:=Q.halo) (b:=radiusB τ) _ h)⟩
     split
     next ht=>
       have hs:∀ i∈v,Y.born i:=(Y.together h hp).1 ht.1
       rw [Y.transmitted (preps X (roster (v.biUnion id).toLeft)) _ h v hp he hk Hx]; refine prod_congr rfl fun i hi=>?_;
       unfold shootsP; rw [if_pos ⟨hp.1 i hi,hs i hi,hA i hi⟩]
       let Z:= Matter.planted X i.toLeft; let W:=Y.full i
       change draws A _=draws Z _
       unfold draws; apply congr_arg choiceS; funext k
       have hP: Village (A.taggedL k) (Z.taggedL k) W:=by
          refine ⟨rfl,rfl,rfl,fun j hj=>?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
          have he:j∈ (roster U.toLeft).place↔ j∈(roster i.toLeft).place:=by
             unfold U; rw [portm]; refine ⟨fun ⟨z,hz,h⟩=> ?_,fun h=>⟨i,hi,h⟩⟩
             exact Y.shadeP hp hz hi (Y.lesserP z (Matter.range (T:=T) (R:=R) (l:=Q.halo) (b:=radiusB τ) _ h)) hj ▸ h
          have hB:j∈ B↔ j∈ (roster i.toLeft).flags:=by rw [← hA i hi,mem_inter]; exact ⟨fun p =>⟨p,hj⟩,fun p=>p.1⟩
          change j∈ (roster U.toLeft).place ↔ j∈ Z.seeds.place; rw [he]
          dsimp only [Z,planted,preps]; unfold Stores.place; simp only [mem_union]; refine or_congr Iff.rfl ?_; exact hB.symm
       refine Beam.weight H (A.taggedL k) (Z.taggedL k) W _ _ he hk Hx (planted_valid X _) (ripeP Y _ _ h) (ripeP Y _ _ h) hP fun u a b hh=> habitat Y _ _ _ h _ _ a b he ⟨hP.wrap _ _ (fun _ _=>rfl), (observe _).1 hh, fun x hX=>?_⟩
       simp only [Contract.covered,mem_biUnion]; constructor
       · rintro ⟨j,hp',ht'⟩; obtain ⟨z,hz,hv⟩:=(onlyP v j).1 hp'; refine ⟨j,Y.shadeP hp hz hi (Y.lesserP z (claim_zoneK R T Q.halo (radiusB τ) _ j hv ht')) hX ▸ hv,ht'⟩
       rintro ⟨j,hj,ht⟩; exact ⟨j,(onlyP v j).2 ⟨i,hi,hj⟩,ht⟩
     next ht=>
       have hv := Y.together h hp; have hb : ¬∀ i∈v,Y.born i:=fun hh=>ht ⟨hv.mpr hh,Hx⟩
       push Not at hb; obtain ⟨i,hi,hb⟩:=hb; exact Eq.symm <| prod_eq_zero hi (if_neg (fun h=>hb h.2.1))
   rw [if_neg (fun h=>Hx h.2),if_neg (fun h=>Hx (hL.mpr h.2))]
end YM.QCD.Beam.Pipe
