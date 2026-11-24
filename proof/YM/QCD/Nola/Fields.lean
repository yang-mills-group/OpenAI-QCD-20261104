import YM.QCD.Nola.Eft
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola.Pads
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι K κ A:Type*} {n : Side} {k:ℕ} [Fintype A]{p:A→Site n}(S:Pads p ι κ)
abbrev Join := {s:Finset (ι⊕κ)// Ac.Spark S.leaves s ∧ s.toLeft.Nonempty}
def unionK (s:S.Join):Support n := Stamp S s.val
def unite (s:S.Join):Patio A:= ham S s.val
lemma plot (s:Finset (Finset (ι⊕κ))) (hs:(s:Set (Finset (ι⊕κ))).PairwiseDisjoint id)(h:(s:Set (Finset (ι⊕κ))).PairwiseDisjoint S.Stamp): ∏ i∈s,S.ham i=S.ham (s.biUnion id):=by
      induction s using Finset.induction_on with
      | empty => symm; apply Subtype.ext; simp only [prod_empty,biUnion_empty]; change S.ping ∅ (light _ (S.grape ∅))=1; simp [ping,grape]
      | insert i s hi ih=>
        rw [prod_insert hi, ih (hs.subset (subset_insert ..)) (h.subset (subset_insert ..)), biUnion_insert]; symm; refine S.ham_union _ _ ?_ ?_
        · apply Finset.disjoint_left.mpr; intro x hx hy; obtain ⟨j,hj,hk⟩:= mem_biUnion.mp hy; exact Finset.disjoint_left.mp (hs (mem_insert_self ..) (mem_insert_of_mem hj) (fun h=>hi (h ▸ hj))) hx hk
        apply Finset.disjoint_left.mpr; intro x hx hy; obtain ⟨j,hj,hk⟩:= mem_biUnion.mp hy; obtain ⟨b,hb,hT⟩:=mem_biUnion.mp hj; exact Finset.disjoint_left.mp (h (mem_insert_self ..) (mem_insert_of_mem hb) (fun hv=>hi (hv ▸ hb))) hx (mem_biUnion.mpr ⟨_,hT,hk⟩)
noncomputable def rang (s: Finset S.Join):Finset (Finset (ι ⊕ κ)):= s.image Subtype.val
noncomputable def unwrap (s:Finset S.Join):= (S.rang s).biUnion id
lemma ham_block (hp:∀ i,S.buys i (1:Alg A)=0)(s:Finset (ι⊕κ))(h:Ac.Spark S.leaves s)(hh:s.toLeft=∅): S.ham s=0:=by
     have hv:s.toRight.Nonempty:=by
                                        obtain ⟨a,h⟩:= h.1; rcases a with a|a
                                        · have he:= mem_toLeft.mpr h; rw [hh] at he; simp at he
                                        exact ⟨_,mem_toRight.mpr h⟩
     apply Subtype.ext; change S.oust _=0; rw [oust,hh,grape,prod_empty,map_one]; obtain ⟨a,ha⟩:= hv; let b:=s.toRight.erase a; have ht:{a}∪b=s.toRight:=by rw [singleton_union,insert_erase ha]
     have hu:b∪{a}= s.toRight:=by rw [union_comm,ht]
     rw [←hu,S.ping_step _ _ (by simp [b])]; change S.ping b (S.ping {a} 1)=0; rw [show S.ping {a}= S.buys a by simp [ping],hp,map_zero]
lemma stroll (s:Finset S.Join) (h: separated (blocked S.unionK) s): Ac.Parts S.leaves (S.unwrap s)=S.rang s ∧ S.ham (S.unwrap s)= ∏ i ∈ s,S.unite i:=by
     have hu: ((S.rang s):Set (Finset (ι⊕κ))).PairwiseDisjoint S.Stamp:=by
           intro i hi j hj H; obtain ⟨a,ha,rfl⟩:=mem_image.mp hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hj; exact ((GasP.close _ _ _).mp h) ha hb (fun hh=> H (congr_arg Subtype.val hh))
     have ht:Ac.Parts S.leaves (S.unwrap s)=S.rang s:= Ac.separates _ _ (fun i hi=> by obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact j.property.1) hu
     refine ⟨ht,(S.plot _ ?_ hu).symm.trans ?_⟩
     · rw [← ht]; apply Ac.different
     unfold rang; rw [prod_image Subtype.val_injective.injOn]; rfl
variable [Fintype ι][Fintype κ]
lemma canvas (hp:∀ i,S.buys i (1:Alg A)=0) : ∑ s:Finset (ι⊕κ),S.ham s= totalP (blocked S.unionK) S.unite:=by
    unfold totalP; rw [tsum_fintype]; simp only [valueP]; rw [← sum_filter]
    let F:Finset (Finset S.Join):=univ.filter (separated (blocked S.unionK)); let P:=F.image S.unwrap
    rw [← sum_subset (subset_univ P) ?inactive, show (∑ i∈P,S.ham i)=∑ i∈ F,S.ham (S.unwrap i) from Finset.sum_image (by
         intro i hi j hj H; have he:S.rang i=S.rang j:= (S.stroll _ (mem_filter.mp hi).2).1.symm.trans ((congr_arg (Ac.Parts S.leaves) H).trans (S.stroll _ (mem_filter.mp hj).2).1); exact image_injective Subtype.val_injective he)]
    · exact sum_congr rfl fun i hi=> (S.stroll i (mem_filter.mp hi).2).2
    case inactive=>
       intro i hi hg
       let A:=Ac.Parts S.leaves i
       have ha:S.ham i=∏ j∈A,S.ham j:=by
                                       conv_lhs=> arg 2; rw [← Ac.reconstruct S.leaves i]
                                       exact (S.plot A (Ac.different ..) (Ac.separate ..)).symm -- syntax
       rw [ha]; by_contra hH; have hw : ∀ a∈A,a.toLeft.Nonempty:=fun a hx=>by by_contra! hh; exact hH (prod_eq_zero hx (ham_block _ hp _ (Ac.lives _ _ hx).2 hh))
       let D: Finset S.Join:= univ.filter (fun v=> v.val∈ A); have hb:S.rang D=A:=by
                                                                                      ext a; constructor
                                                                                      · intro h; obtain ⟨v,hv,rfl⟩:=mem_image.mp h; exact (mem_filter.mp hv).2
                                                                                      intro h; refine mem_image.mpr ⟨⟨a,(Ac.lives _ _ h).2,hw a h⟩,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
       apply hg; refine mem_image.mpr ⟨D, mem_filter.mpr ⟨mem_univ _,?_⟩,(by unfold unwrap; rw [hb]; exact Ac.reconstruct ..)⟩
       rw [GasP.close]; exact fun i hi j hj he=> (Ac.separate _ _) ((mem_filter.mp hi).2) ((mem_filter.mp hj).2) (fun hz=>he (Subtype.ext hz))
end YM.QCD.Nola.Pads
