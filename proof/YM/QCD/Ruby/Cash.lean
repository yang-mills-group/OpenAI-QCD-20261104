import YM.QCD.Ruby.Bahn
/-! # regroup dose. Pre-quotient, restrict actual flags -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}
variable (Y:Hue c N ι) (X:Rail c N β)
local notation "J"=> footD Y X
def valid (v:Finset (Cart ι β)):Prop:= (∀ i∈v,gemD Y X i) ∧ (v:Set _).PairwiseDisjoint (scopeK Y X)
def books (X:Rail c N β)(v:Finset (Cart ι β)):= (v.biUnion id).toLeft.biUnion (oriD X)
lemma badge_sum (v:Finset (Cart ι β)): books X v=v.biUnion (badgeK X):=by ext i; simp only [books,badgeK,mem_biUnion, mem_toLeft,id_eq]; grind
lemma lucky (v:Cart ι β) (hp:suit Y X v): valid Y X (Ac.Parts J v):=by
     let V:= Ac.Parts J v; refine ⟨fun b hb=> ?_,Ac.separate ..⟩
     obtain ⟨hV,h⟩:= Ac.lives J _ hb
     have hv:b.toLeft⊆ v.toLeft:=fun j hj=>mem_toLeft.mpr (hV (mem_toLeft.mp hj))
     have hh i (hi:i∈b.toRight): ¬Disjoint (Y.bud i) (badgeK X b):=by
        obtain ⟨j,hj,hx⟩:=not_disjoint_iff.mp (hp.2 i (mem_toRight.mpr (hV (mem_toRight.mp hi))))
        obtain ⟨z,hz,hx⟩:=mem_biUnion.mp hx
        refine not_disjoint_iff.mpr ⟨j,hj,mem_biUnion.mpr ⟨z,mem_toLeft.mpr ?_,hx⟩⟩
        have he : .inl z∈ v:=mem_toLeft.mp hz
        rw [← Ac.reconstruct J v] at he; obtain ⟨a,ha,hh⟩:=mem_biUnion.mp he
        suffices he:a=b from he ▸ hh
        exact by_contra (fun hn=> Finset.disjoint_left.mp ((Ac.separate ..) ha hb hn) (mem_biUnion.mpr ⟨.inl z,hh,(X.addr z).part hx⟩) (mem_biUnion.mpr ⟨.inr i,mem_toRight.mp hi,hj⟩)) -- Ac.separate .. signature
     refine ⟨⟨(fun j hj i hi=>hp.1 _ (hv hj) _ (hv hi)),hh⟩,?_,h⟩
     obtain ⟨i,hi⟩:=h.1; rcases i with i|i; · exact ⟨i,mem_toLeft.mpr hi⟩
     obtain ⟨j,hx,hj⟩:=not_disjoint_iff.mp (hh i (mem_toRight.mpr hi)); obtain ⟨j,hj,hx'⟩:=mem_biUnion.mp hj; exact ⟨j,hj⟩
lemma stems (t:Finset (Cart ι β))(he: valid Y X t): suit Y X (t.biUnion id):=by
    let k:= t.biUnion id; constructor
    · apply (GasP.close β _ k.toLeft).2; intro i hi j hj hx; obtain ⟨p,hp,hi⟩:=mem_biUnion.mp (mem_toLeft.mp hi); obtain ⟨q,hq,hj⟩:=mem_biUnion.mp (mem_toLeft.mp hj)
      by_cases hv: p=q
      · subst q; exact ((GasP.close β _ _).1 (he.1 p hp).1.1) (mem_toLeft.mpr hi) (mem_toLeft.mpr hj) hx
      exact ((he.2 hp hq hv).mono_left (subset_biUnion_of_mem J hi)).mono_right (subset_biUnion_of_mem J hj)
    intro i hi; obtain ⟨p,hp,hi⟩:=mem_biUnion.mp (mem_toRight.mp hi); intro hn; apply (he.1 p hp).1.2 i (mem_toRight.mpr hi); apply hn.mono_right; change badgeK X p⊆books X t; rw [badge_sum]; exact subset_biUnion_of_mem _ hp
noncomputable def paid (t:ℝ)(U:Grid c)(v:Cart ι β): EvenA c N:= if suit Y X v∧ flags t U=badgeK X v then ∏ i∈v,flower Y X U i else 0
noncomputable def fold (t:ℝ)(U:Grid c)(v:Finset (Cart ι β)): EvenA c N:=if valid Y X v∧ flags t U=books X v then ∏ i∈v,payer Y X t U i else 0
lemma earning (U:Grid c)(v:Finset (Cart ι β))(hp:valid Y X v): paid Y X t U (v.biUnion id)=fold Y X t U v:=by
    have hx:Ac.Parts J (v.biUnion id)=v:= Ac.separates _ _ (fun i hi=>(hp.1 i hi).2.2) hp.2
    have he:=(Ac.different J (v.biUnion id)); rw [hx] at he
    unfold fold paid; by_cases hK:flags t U=books X v; swap; · rw [if_neg (fun h=>hK h.2),if_neg (fun h=>hK h.2)]
    rw [if_pos ⟨stems Y X v hp,hK⟩,if_pos ⟨hp,hK⟩,prod_biUnion he]
    rw [badge_sum] at hK; apply prod_congr rfl; intro i hi; unfold payer; rw [if_pos]; try rfl
    ext j; rw [hK]; constructor
    · intro h; obtain ⟨hj,he⟩:=mem_inter.mp h; obtain ⟨x,hx,hj⟩:=mem_biUnion.mp hj
      suffices h:x=i from h ▸ hj
      exact by_contra (fun hx'=> Finset.disjoint_left.mp (hp.2 hx hi hx') (badge_s Y X x hj) he)
    intro h; exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,hi,h⟩,badge_s Y X _ h⟩
lemma timeK (U:Grid c)(s:Finset (Plot Y X)): tK (Trail Y X t) t U s= fold Y X t U (s.image Subtype.val):=by
    unfold tK fold; refine if_congr (and_congr ?_ ?_) ?_  rfl
    · rw [GasP.close]; constructor
      · intro h; refine ⟨fun i hi=>?_,fun i hi j hj hn=>?_⟩
        · obtain ⟨p,hp,rfl⟩:=mem_image.mp hi; exact p.2
        obtain ⟨p,hp,rfl⟩:=mem_image.mp hi; obtain ⟨q,hq,rfl⟩:=mem_image.mp hj; exact h hp hq (fun h=> hn (h ▸ rfl))
      intro h i hi j hj he; exact h.2 (mem_image_of_mem Subtype.val hi) (mem_image_of_mem Subtype.val hj) (fun hh=>he (Subtype.ext hh))
    · rw [badge_sum,image_biUnion]; rfl
    rw [prod_image Subtype.val_injective.injOn]; rfl
lemma continuum (V:Grid c)(hv:Y.Tall t)(u:Finset β)(p:Finset ι):paid Y X t V (u.disjSum p)= tK X t V u*∏ i∈p,sparkY Y V i :=by
    unfold paid tK badgeK suit; rw [toLeft_disjSum,toRight_disjSum]; unfold badgeK; rw [toLeft_disjSum]; split
    next h=> rw [if_pos ⟨h.1.1,h.2⟩,prod_disjSum]; rfl
    next h=> split
             next hx=> have hg: ¬ ∀ i∈p, ¬Disjoint (Y.bud i) (flags t V):=by rw [hx.2]; intro h'; exact h ⟨⟨hx.1,h'⟩,hx.2⟩
                       push Not at hg; obtain ⟨i,hi,hg⟩:=hg; have hf: sparkY Y V i=0:=by unfold sparkY; rw [show Y.mean i V=0 from by_contra (fun hh=>hv.non i V hh hg),exp_zero,sub_self]
                       rw [prod_eq_zero hi hf,mul_zero]
             next hx=> rw [zero_mul]
lemma ranges (g:Cart ι β) (V:Grid c): fold Y X t V (Ac.Parts J g)=paid Y X t V g:=by
    by_cases hv:suit Y X g; · exact ((earning Y X (t:=t) V _ (lucky Y X g hv)).symm).trans (congr_arg _ (Ac.reconstruct J g))
    rw [fold,if_neg (fun hp=> hv ((show _=g from Ac.reconstruct J g) ▸ stems Y X _ hp.1)),paid,if_neg (fun h=>hv h.1)]
lemma trust (K:EvenA c N)(U:Grid c) (h:HasSum (paid Y X t U) K): HasSum (tK (Trail Y X t) t U) K:=by
    let V (p:Cart ι β):=Ac.Parts J p; let P:=Trail Y X t; let w:= fold Y X t U
    have he: Injective V:= fun i j h=>by rw [← Ac.reconstruct J i,← Ac.reconstruct J j, show Ac.Parts J i=Ac.Parts J j from h]
    have hp: HasSum w K:= by
       refine (he.hasSum_iff ?_).1 (h.congr_fun fun i=>ranges Y X i U)
       intro i hi; unfold w fold; rw [if_neg]; intro hx; exact hi ⟨i.biUnion id, Ac.separates _ _ (fun j hj=> (hx.1.1 j hj).2.2) hx.1.2⟩
    let f i:=image (fun j:Plot Y X=>j.val) i
    refine (((show Injective f from image_injective Subtype.val_injective).hasSum_iff (f:=w) ?_).2 hp).congr_fun fun i => ?_
    · intro i hi; unfold w fold; rw [if_neg]; intro hx; apply hi; let X':=i.preimage Subtype.val (Subtype.val_injective (p:=fun p : Cart ι β=>gemD Y X p)).injOn
      refine ⟨X',?_⟩; ext j; constructor
      · intro h; obtain ⟨p,hp,rfl⟩:=mem_image.mp h; exact mem_preimage.mp hp
      intro hj; exact mem_image.mpr ⟨⟨j,hx.1.1 j hj⟩,mem_preimage.mpr hj,rfl⟩
    exact timeK ..
lemma plenary (U:Grid c)(hp:Summable (tK X t U))(he:Y.Tall t)(hV: Summable fun i=>Y.mean i U)(hg:Summable fun i => ‖sparkY Y U i‖): HasSum (tK (Trail Y X t) t U) ((∑' i,tK X t U i)*NormedSpace.exp (∑' i,Y.mean i U)):=by
    apply trust; apply ((packEquiv β ι).hasSum_iff).mp
    let g s:= ∏ i∈s,sparkY Y U i
    have hv:Summable fun i=> ‖g i‖:= Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun _=> Finset.norm_prod_le ..) (summable_finsetProd_of_summable_nonneg (fun _=> norm_nonneg _) hg)
    have hh: HasSum g (NormedSpace.exp (∑' i,Y.mean i U)):= by
       refine hasSum_of_subseq_of_summable hv (p:=atTop) (s:=Finset.powerset) (tendsto_atTop.2 ?_) ?_
       · intro i; filter_upwards [eventually_ge_atTop (i.biUnion id)] with z hz; exact fun j hj=> mem_powerset.mpr ((subset_biUnion_of_mem id hj).trans hz)
       unfold g sparkY; simp_rw [← flicker]; exact NormedSpace.exp_continuous.continuousAt.tendsto.comp hV.hasSum
    exact (toss_big hp.hasSum hh hp.norm hv).congr_fun (fun i=> continuum Y X U he i.1 i.2)
end YM.QCD.Ruby
