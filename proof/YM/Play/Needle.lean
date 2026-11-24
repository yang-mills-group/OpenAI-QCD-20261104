import YM.MassiveQCD.Stitch.Mint
/-!
# Summing a compass inside its settled spot.

 Finite exact conditional statement on *all* Geist roots in permit. No independence
 assertion retained across a reading. At closure passes explicitly to high-spin Wick
 operation; remains in massive scheme. Does not discard any power paid without reason.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj
open scoped Finset Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}{P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
variable {R:Ratio c f}{t:ℝ}
variable (G:Send R N D)
local notation "A"=> Modes f N
local notation "B"=> Modes c N
local notation "WZ"=> Junta c f N
variable {q:I→Bool}{o:I→Site f}(hw:X.Wave t q o) (M:Fj D E J→Support c) (h:Cove.Count G P M)
open Further.ShellBirth49.Fusing Collide
local notation "Γ"=> Fj D E J
/-- all contributing derivative operators must touch original main support.
 Reorder licenses using commuting map; `fuel` kills the empty query too. -/
def sourceE (P:Rise f N E J)(s : Finset E): Support f:= s.biUnion fun i=>(P.row i).support
def Burke (P:Rise f N E J)(G:Send R N D)(s : Finset (Fj D E J)): Prop:= ∀ i∈ ops s,¬ Disjoint (sourceE P (leftE s)) (G.rooms i)
namespace TabletV
open Stitch.Tablet
include hw
lemma brook (s:Finset Γ)(U:Grid f)(he:Fj.spent s=∅) (hp:X.dye t G s U≠0) : Burke P G s:=by
    let V:=sourceE P (leftE s); intro i hi h₀; apply hp; apply Subtype.ext; apply vista (Keys c N); intro j
    let Y:= X.made t U s; let p := pin (∅:Finset D) (leftE s) (∅:Finset J)
    have hY:Y=X.made t U p:=by simp only [p,Tablet.made,he,Y,pinX,pinK]
    let k:=near A B (scrape (Keys f N) j (light _ Y))
    have hv: hooks R V |> region |> fun H => k ∈ H :=by
       have hz: V=coreW G P p:=by
         ext x; simp only [V,sourceE,coreW,p,pin,mem_biUnion,mem_disjSum]; -- inspect
         constructor
         · rintro ⟨j,hj,hx⟩; exact ⟨Sum.inr (.inl j),by simp [hj],hx⟩
         rintro ⟨j,hj,hx⟩; rcases j with j|j|j
         · simp at hj
         · exact ⟨j,by simpa using hj,hx⟩
         simp at hj
       unfold k; rw [hY,hz]; exact remit G p _ ((X.lights_made G hw p U).2 j)
    change scrape (Keys c N) _ (carry _ _ _)=scrape _ _ 0; rw [map_zero,wing]; change wipe A B _ (axle G U s k)=0
    have ht: Disjoint (hooks (F:=N) R V) (hooks R (G.rooms i)):=Finset.disjoint_left.mpr (fun a ha hb=> Finset.disjoint_left.mp h₀ ((hooked ..).mp ha) ((hooked ..).mp hb))
    have h':bucks G i U k=0:=by
      have hx:= DFunLike.congr_fun ((G.weld U i).parts ht k hv).eq (1:Alg WZ); change bucks G i U (1*k)=bucks G i U 1 * k at hx; rwa [one_mul,show bucks G i U 1=0 from G.fuel U i,zero_mul] at hx
    unfold axle; rw [← noncommProd_erase_mul _ hi,_root_.ContinuousLinearMap.mul_apply,h',map_zero,map_zero] -- check

lemma vibrant (s:Finset Γ)(U:Grid f)(he:Fj.spent s=∅) (hp:X.hue t G s U≠0): Burke P G s:=by
   unfold Stitch.Tablet.hue at hp; split at hp; exact brook X G hw s U he hp; exact (hp rfl).elim
omit hw
lemma lush (s:Finset Γ)(hp:s.Nonempty)(he:Fj.spent s=∅) (h:Burke P G s): (leftE s).Nonempty:=by
   by_contra! hv; have hm:leftE s=∅:=by grind
   obtain ⟨i,hi⟩:=hp; cases i with
   | inl i => apply h i (by simpa [ops] using hi); simp only [hm,sourceE,biUnion_empty]; exact Finset.disjoint_empty_left _
   | inr i=> rcases i with i|i
             · have hh:i∈leftE s:=(by simpa [leftE] using hi); simp [hm] at hh
             have hh:i∈spent s:=(by simpa [spent] using hi); simp [he] at hh
-- permission
abbrev choiceE (M:Fj D E J→Support c)(p:Finset (Fj D E J)): Finset (Finset (Finset (Fj D E J))):=p.powerset.powerset.filter fun q=> q∈taxes M
lemma scaleV (p:Finset Γ): choiceE M p = p.powerset.image (fun i=>parts M i):=by
    ext i; constructor
    · intro hi; obtain ⟨hp,hq⟩:= mem_filter.mp hi
      refine mem_image.mpr ⟨_,mem_powerset.mpr ?_,uncluttered M i hq.1 hq.2⟩
      intro j hj; obtain ⟨b,hb,hj⟩:=mem_biUnion.mp hj; exact (mem_powerset.mp ((mem_powerset.mp hp) hb)) hj
    intro hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hi; refine mem_filter.mpr ⟨mem_powerset.mpr (?_), Collide.separate M b,fun i hi=>(living M hi).2⟩; -- subtype goals
    intro i hi; refine mem_powerset.mpr fun j hj=>mem_powerset.mp hb ?_; rw [←recombine M b]; exact mem_biUnion.mpr ⟨i,hi,hj⟩
include hw h
lemma grassV (U:Grid f)(p:Finset Γ): (∑ s∈choiceE M p, s.prod (fun j=> X.hue t G j U))= ∑ j∈p.powerset,X.hue t G j U:=by
   rw [scaleV,sum_image]; refine sum_congr rfl fun i _=>?_ ; exact (hue_product X G hw h (parts M i) U (Collide.separate M i) (erases M i)).symm.trans (congr_arg (fun i=> X.hue t G i U) (recombine M i))
   intro i hi j hj ht; exact Eq.trans (recombine M i).symm ((congr_arg (fun i=> i.biUnion id) ht).trans (recombine M j))
omit h hw
/-- unmarked often taxed. take the funded restriction -/
def plume (P:Rise f N E J)(G:Send R N D)(M:Fj D E J→Support c)(p:Finset (Fj D E J)):= p.powerset.filter (fun j=>spark M j ∧ Burke P G j)
abbrev chest (P:Rise f N E J)(G:Send R N D)(M:Fj D E J→Support c)(p:Finset (Fj D E J)): Finset (Finset (Finset (Fj D E J))):= (plume P G M p).powerset.filter (fun s : Finset (Finset (Fj D E J))=> (s:Set (Finset (Fj D E J))).PairwiseDisjoint fun i=> i.biUnion M)
lemma spentP (s p:Finset Γ)(hs:s⊆p) (he:spent p=∅) : spent s=∅:=by
    ext i; refine ⟨fun h=> ?_,fun h=> (Finset.notMem_empty _ h).elim⟩; rw [← he]; exact Finset.mem_toRight.mpr (Finset.mem_toRight.mpr (hs (Finset.mem_toRight.mp (Finset.mem_toRight.mp h))))
include h hw
lemma drafted (U:Grid f)(p:Finset Γ) (he:spent p=∅): (∑ s∈chest P G M p, s.prod (fun j=> X.hue t G j U))=∑ j∈p.powerset,X.hue t G j U:=by
   rw [← grassV X G hw M h U p]
   apply sum_subset
   · intro i hi; obtain ⟨hp,hq⟩:=mem_filter.mp hi; have hf:= mem_powerset.mp hp
     exact mem_filter.mpr ⟨mem_powerset.mpr (hf.trans (filter_subset _ _)),hq,fun j hj=>(mem_filter.mp (hf hj)).2.1⟩
   intro i hi hx; contrapose! hx; obtain ⟨hp,hq⟩:=mem_filter.mp hi
   exact mem_filter.mpr ⟨mem_powerset.mpr fun j hj=>mem_filter.mpr ⟨(mem_powerset.mp hp) hj,(hq.2 j hj), vibrant X G hw _ _ (spentP j p (mem_powerset.mp (mem_powerset.mp hp hj)) he) (fun he=>hx (Finset.prod_eq_zero hj he))⟩, hq.1⟩

/- Can use smaller roof outside arbour. Inactive ops kill in every actual spin word. -/
omit h in
lemma arbor (U:Grid f)(p:Finset Γ)(he:spent p=∅)(hh:∀ i⊆p,Burke P G i→ Healthy t (brimW G P i) U)(i:Finset Γ)(hi:i⊆p): X.hue t G i U=X.dye t G i U:=by
   unfold Stitch.Tablet.hue
   split; exact rfl
   next hn=> symm; by_contra h
             have hv:=spentP i p hi he; have hg:=brook X G hw i U hv h
             apply hn; unfold closeS; rw [hv]; simp only [Rise.spare,coe_empty,Set.pairwise_empty,true_and,Rise.wish,biUnion_empty]; exact (Finset.disjoint_iff_inter_eq_empty.mp (hh i hi hg).symm).symm
/-- Full conditional **short** Wick reading on paid word projection. -/
lemma oak (U:Grid f)(O:Finset D)(Ve:Finset E) (hh:∀ i⊆pin O Ve (∅:Finset J),Burke P G i→Healthy t (brimW G P i) U):
   let T:= (wipeL G U).comp ((birth (∑ i∈O,G.treats i U)).comp (nearL f c N)); let H':= ∑ i∈Ve,X.read t U i
   light Y' (∑ s∈chest P G M (pin O Ve ∅), s.prod (fun j=>X.hue t G j U))=carry S T (light _ (NormedSpace.exp H') ) :=by
    intro L H'; let W:=pin O Ve (∅:Finset J)
    let B' i:= light Y' (X.dye t G i U)
    rw [drafted X G hw M h U W (pinK ..),map_sum,sum_congr rfl (f:=fun j=>light Y' (X.hue t G j U)) (g:=B') (fun i hi=> congr_arg (light Y') (arbor X G hw U W (pinK ..) hh i (mem_powerset.mp hi)))]
    -- use nested powerset identity.
    let C:= O.powerset.product Ve.powerset; let g(i: Finset D×Finset E):=pin i.1 i.2 (∅:Finset J)
    have hE : W.powerset=C.image g:=by
       ext i; constructor
       · intro h; refine mem_image.mpr ⟨(ops i,leftE i), ?_,?_⟩
         · have hz:=mem_powerset.mp h; exact mem_product.mpr ⟨mem_powerset.mpr (fun j hj=>inl_mem_disjSum.mp (hz (Finset.mem_toLeft.mp hj))),mem_powerset.mpr (fun j hj=> inl_mem_disjSum.mp (inr_mem_disjSum.mp (hz (mem_toRight.mp (mem_toLeft.mp hj)))))⟩
         unfold g; dsimp only; rw [←spentP i W (mem_powerset.mp h) (pinK ..), pinch]
       rintro h; obtain ⟨j,hj,rfl⟩:=mem_image.mp h; apply mem_powerset.mpr; obtain ⟨hx,hy⟩:=mem_product.mp hj; exact disjSum_mono (mem_powerset.mp hx) (disjSum_mono (mem_powerset.mp hy) (Subset.refl _))
    change (∑ i∈W.powerset,B' i)=_; rw [hE,sum_image]; swap
    · intro i _ j _ h; exact Prod.ext (by simpa only [g,pinC] using congr_arg ops h) (by simpa only [g,pinX] using congr_arg leftE h)
    apply Ribbon.vista (Keys c N); intro b
    unfold C; change scrape (Keys c N) b (∑ x∈O.powerset ×ˢ Ve.powerset,B' (g x))=_; rw [sum_product,map_sum,wing]; unfold L; rw [← dripe _ (fun i j=>G.hat U i j) O]; dsimp only [_root_.ContinuousLinearMap.comp_apply]; rw [show NormedSpace.exp H'=_ from flicker (fun i=> X.read t U i) Ve,_root_.sum_apply]; rw [map_sum (wipeL G U)]; apply sum_congr rfl; intro j _
    simp only [map_sum]; apply sum_congr rfl; intro k _; change scrape (Keys c N) _ (carry S _ _)=_; rw [wing]; simp only [tunnel,axle,g,Tablet.made,pinX,pinK,pinC,prod_empty,mul_one]; rfl

end TabletV
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.TabletV.oak
