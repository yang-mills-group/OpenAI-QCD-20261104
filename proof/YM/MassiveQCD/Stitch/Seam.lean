import YM.MassiveQCD.Stitch.Fold
/-! # Patch and root-support propagation; permitted bindings for MARKER charges conditional on loans -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}{P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
variable {R:Ratio c f}{t:ℝ}
variable (G:Send R N D)
local notation "A"=> Modes f N
local notation "B"=> Modes c N
local notation "W"=> Junta c f N
variable {q:I→Bool}{o:I→Site f}(hw:X.Wave t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
include hw
lemma extent (s:Finset (Fj D E J)) : (X.markers s).image o ⊆ coreW G P s:=by
   intro i hi; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; rcases mem_union.mp hk with he|he
   · obtain ⟨i,hi,he'⟩:= mem_biUnion.mp he; exact mem_biUnion.mpr ⟨Sum.inr (Sum.inl i), by simpa [leftE] using hi,hw.spotE i (mem_image_of_mem _ he')⟩
   obtain ⟨i,hi,he'⟩:= mem_biUnion.mp he; exact mem_biUnion.mpr ⟨Sum.inr (Sum.inr i),by simpa [spent] using hi, hw.spotK i (mem_image_of_mem _ he')⟩
include h in
lemma endowment (s:Finset (Fj D E J)) : (X.markers s).image (R.parent∘o)⊆s.biUnion M:=by
   rw [← Finset.image_image]; exact (Finset.image_subset_image ((X.extent G hw s).trans (native_sub G P s))).trans (totalW G P h s)
omit hw
lemma remit (s:Finset (Fj D E J))(x:Alg (Keys f N))(h:x∈region (limits (coreW G P s))): near A B x∈ region (hooks R (coreW G P s)):=by
   apply effects _ _ x h; intro i hi; change embed (ha ..) _∈_; rw [embed_atom]; apply marked; rw [hooked,rootA]; exact (mem_filter.mp hi).2
lemma lamp (s: Finset (Fj D E J))(y:Grid f)(x:Alg (Keys f N))(he:x∈ region (limits (coreW G P s))): axle G y s (near A B x) ∈ region (hooks R (coreW G P s)):= (forces G P y s).keeps (Subset.refl _) _ (remit G s x he)
private lemma hatch (s:Finset (Fj D E J))(y:Grid f)(x: Alg (Keys f N))(ht:x∈ region (limits (coreW G P s)))(Z:Support c)(he:(halo G.trim (coreW G P s)).image R.parent ⊆ Z): tunnel G s y x ∈ region (limits Z):=by
   refine effects (wipe A B (G.shortP y)) ?_ _ (lamp G s y x ht); intro i hi; rcases splits_index i with ⟨v,rfl⟩|⟨v,rfl⟩
   · change ha _ _ _ v∈_ at hi; rw [hooked,rootA] at hi; rw [wiper]; refine Subalgebra.sum_mem _ (fun j _=>?_); by_cases hx:G.shortP y v j=0; · rw [hx,zero_smul]; exact Subalgebra.zero_mem _
     apply Subalgebra.smul_mem; apply marked; exact mem_filter.mpr ⟨mem_univ _,he (mem_image.mpr ⟨_, (Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr hi) (G.sleeps v j y hx)), R.embed_parent _⟩)⟩
   change hb _ _ _ v∈_ at hi; rw [hooked,rootB] at hi; rw [tails]; apply marked; exact mem_filter.mpr ⟨mem_univ _,he (mem_image.mpr ⟨R.embed _,halo_subset _ _ hi,R.embed_parent _⟩)⟩
include hw h in
lemma lights_hue (s:Finset (Fj D E J))(U:Grid f): lights (X.markers s) (s.biUnion M) (R.parent∘o) q (X.hue t G s U):=by
    unfold hue; split
    · obtain ⟨hp,hp'⟩:=X.lights_made G hw s U; exact ⟨politeStep _ hp rfl,reCarry _ _ _ (fun x hx=> hatch G _ U x hx _ (by
                                                                                                                                     exact (Finset.image_subset_image (show halo _ _⊆ brimW G P s by rw [brim_eq]; exact Corona.halo_mono (by omega) (Subset.refl _))).trans (totalW G P h s))) _ hp'⟩
    exact ⟨polite_nil ..,clad.nil _⟩
lemma unionM (t:ℝ)(U:Grid f){s w:Finset (Fj D E J)}(hd:Disjoint s w): X.made t U (s∪w)=X.made t U s*X.made t U w:=by
  have ht: leftE (s∪w)=leftE s∪leftE w:=by ext; simp [leftE]
  have hz: spent (s∪w)=spent s∪spent w:=by ext; simp [spent]
  have hp: Disjoint (leftE s) (leftE w):=by
    refine Finset.disjoint_left.mpr fun i hi hv=> Finset.disjoint_left.mp hd (show Sum.inr (Sum.inl i) ∈ s by simpa [leftE] using hi) (show Sum.inr (Sum.inl i)∈ w by simpa [leftE] using hv)
  have hv: Disjoint (spent s) (spent w):=by
    refine Finset.disjoint_left.mpr fun i hi hv=> Finset.disjoint_left.mp hd (show Sum.inr (Sum.inr i)∈s by simpa [spent] using hi) (show Sum.inr (Sum.inr i)∈ w by simpa [spent] using hv)
  unfold Tablet.made; rw [ht,hz,prod_union hp,prod_union hv]; ring

include h hw
noncomputable abbrev nearL (f c:Side)(N:ℕ) :=LinearMap.toContinuousLinearMap (near (Modes f N) (Modes c N)).toLinearMap
noncomputable abbrev wipeL (U:Grid f):Alg (Junta c f N)→L[ℂ] Fields c N:=LinearMap.toContinuousLinearMap (wipe A B (G.shortP U)).toLinearMap
lemma textured (s w:Finset (Fj D E J))(U:Grid f)(hp:Disjoint s w)(he:Disjoint (s.biUnion M) (w.biUnion M)): X.dye t G (s∪w) U=X.dye t G s U* X.dye t G w U:=by
   let NN:=carry S (nearL f c N); let p (i:Finset (Fj D E J)):= (X.made t U i).val; let W₁ (i:Finset (Fj D E J)):=carry S (axle G U i); let WW:= carry S (wipeL G U); have ht(i):clad (hooks (F:=N) R (coreW G P i)) (NN (p i)):= reCarry (nearL f c N) (limits _) _ (fun x h=>remit G i x h) _ (X.lights_made G hw i U).2; apply Subtype.ext; change carry S _ _ = carry S _ _*carry S _ _; unfold tunnel; simp_rw [← composes]; rw [unionM X t U hp];
   change WW (carry S (axle G U (s∪w)) (NN (p s*p w)))=WW (W₁ s _) *WW (W₁ w _); rw [show NN (p s*p w) = NN (p s)*NN (p w) from ledger_alg (near A B) (fun x=> (embed_grade _ x).symm) ..,join_ax G U hp,widespread _ _ (forces G P U s) (forces G P U w) (rotor G P h he) (ht _) (ht _)]; exact ledger_alg (wipe ..) (fun x=>(exterior_parity _ x).symm) ..
lemma hueSpare {U:Grid f}{s w:Finset (Fj D E J)}(hp:Disjoint s w)(he:Disjoint (s.biUnion M) (w.biUnion M)): X.hue t G (s∪w) U=X.hue t G s U *X.hue t G w U:=by
    unfold hue; rw [spares G P h he,close_join G P t h U he,textured X G hw h s w U hp he]; split_ifs <;> simp_all
omit h hw
lemma hue_empty (t:ℝ)(U:Grid f): X.hue t G ∅ U=1:=by
   have ha:spent (∅:Finset (Fj D E J))=∅:=by ext; simp [spent];
   have hb:leftE (∅:Finset (Fj D E J))=∅:=by ext; simp [leftE];
   have hz:ops (∅:Finset (Fj D E J))=∅:=by ext; simp [ops];
   unfold hue; rw [if_pos (by simp [Rise.spare,ha,closeS,Rise.wish,brimW])]; apply Subtype.ext
   change carry S _ _=1; have he: X.made (D:=D) t U ∅=1:=by simp [Tablet.made,hb,ha]
   rw [he,show (1:Tine f N I).val=stake (Keys f N) ∅ 1 from (Eq.trans (quiet ..) (map_one _)).symm,speaks,tunnel]; rw [show axle G U (∅:Finset (Fj D E J))=1 from by simp [axle,hz]]; rw [show (LinearMap.toContinuousLinearMap _).comp _ _= (1:Fields c N) from ?_,quiet,map_one]; change wipe A B _ (near _ _ 1)=1; rw [map_one,map_one]
include h hw
open Further.ShellBirth49.Fusing Collide
lemma hue_product (s: Finset (Finset (Fj D E J)))(U:Grid f)(hp:(s:Set (Finset (Fj D E J))).PairwiseDisjoint (fun p=>p.biUnion M))(hr:(s:Set (Finset (Fj D E J))).PairwiseDisjoint id):
    X.hue t G (s.biUnion id) U=∏ p∈s,X.hue t G p U:=by
    induction s using Finset.induction_on with
    | empty=> rw [biUnion_empty,hue_empty,prod_empty]
    | insert i s hi ih=>
      have hQ : Disjoint i (s.biUnion id) := Finset.disjoint_left.mpr (fun j hj hk=>by
        obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hk; exact Finset.disjoint_left.mp (hr (mem_insert_self ..) (mem_insert_of_mem hk) (fun he=>hi (he ▸ hk))) hj hz)
      have hP : Disjoint (i.biUnion M) ((s.biUnion id).biUnion M) := Finset.disjoint_left.mpr fun j hj hk=>by
        obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hk; obtain ⟨p,hp',hk⟩:=mem_biUnion.mp hk; exact Finset.disjoint_left.mp (hp (mem_insert_self ..) (mem_insert_of_mem hp') (fun he=> hi (he ▸ hp'))) hj (mem_biUnion.mpr ⟨k,hk,hz⟩)
      rw [biUnion_insert,id_eq,prod_insert hi,hueSpare X G hw h hQ hP]; apply congr_arg
      exact ih (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert ..)) hp) (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert ..)) hr)
end Tablet
end YM.MassiveQCD.Stitch
