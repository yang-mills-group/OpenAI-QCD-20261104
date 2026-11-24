import YM.QCD.Gas.Atrium
/-! # Optional attachments disjoint except per catalogue. exact bank entries -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.GasP
open Push.AbsoluteSums Partition Relation Graph Ursell Finset Gas Function RG Lattice Wilson Trees
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Classical Topology
variable {ι K κ:Type*}[NormedCommRing K][NormOneClass K][NormedAlgebra ℚ K][NormedAlgebra ℝ K][CompleteSpace K]
variable {n:Side}(p d : ι→ Support n)(q:κ→ Support n) (W: Support n)(u:ι→K)(g:κ→K)
-- same site planet
open NormedSpace
local notation "X"=> Finset ι
local notation "J"=>ι⊕Support n
local notation "U"=>Finset J
-- density prior to attachment. Hard vs Soft exact
noncomputable def ahead (v:X):K:= if obscures p d W v then ∏ i∈v,u i else 0
noncomputable def pole (v:X)(s:Finset κ):K:=ahead p d W u v * valueP (blocked q) (omission q g (v.biUnion p)) s
abbrev scaleU := ∑' k, termP (blocked q) g k
def harvest (v:Finset (ι⊕κ)): K := if (v:Set (ι⊕κ)).PairwiseDisjoint (Sum.elim p q) ∧ v.toLeft.biUnion d=W then ∏ i∈v,Sum.elim u g i else 0

lemma close (A:Type*)(p : A→ Support n)(v: Finset A):separated (blocked p) v ↔ (v:Set A).PairwiseDisjoint p:= by
   constructor
   · intro h i hi j hj hk; exact Finset.disjoint_left.mpr fun x hx hh=> h _ hi _ hj hk (.inr ⟨x,hx,hh⟩)
   intro h i hi j hj he hc; rcases hc with ht|⟨x,hx,hh⟩; · exact he ht
   exact Finset.disjoint_left.mp (h hi hj he) hx hh
lemma allies (v:X)(s:Finset κ): harvest p d q W u g (v.disjSum s)= pole p d q W u g v s:=by
   have he : ((v.disjSum s): Set (ι⊕κ)).PairwiseDisjoint (Sum.elim p q) ↔ separated (blocked p) v ∧ separated (blocked q) s∧∀ x∈s,Disjoint (v.biUnion p) (q x):=by
      rw [close,close]; constructor
      · intro h
        constructor
        · exact fun i hi j hj hn=> h (show Sum.inl i∈v.disjSum s from inl_mem_disjSum.mpr hi) (show Sum.inl j∈v.disjSum s from inl_mem_disjSum.mpr hj) (Sum.inl_injective.ne hn)
        constructor
        · exact fun i hi j hj hn=> h (show Sum.inr i∈v.disjSum s from inr_mem_disjSum.mpr hi) (show Sum.inr j∈v.disjSum s from inr_mem_disjSum.mpr hj) (Sum.inr_injective.ne hn)
        intro x hx; refine Finset.disjoint_left.mpr fun j hj hn=> ?_; obtain ⟨z,hz,hj⟩:=mem_biUnion.mp hj; exact Finset.disjoint_left.mp (h (show Sum.inl z∈ v.disjSum s from inl_mem_disjSum.mpr hz) (show Sum.inr x∈v.disjSum s from inr_mem_disjSum.mpr hx) (by simp)) hj hn
      rintro ⟨hA,hB,hC⟩ i hi j hj hn; simp only [mem_coe] at hi hj; rcases i with i|i <;> rcases j with j|j
      · exact hA (inl_mem_disjSum.mp hi) (inl_mem_disjSum.mp hj) (fun he=> hn (congr_arg _ he))
      · exact (hC j (inr_mem_disjSum.mp hj)).mono_left (subset_biUnion_of_mem p (inl_mem_disjSum.mp hi))
      · exact ((hC i (inr_mem_disjSum.mp hi)).mono_left (subset_biUnion_of_mem p (inl_mem_disjSum.mp hj))).symm
      exact hB (inr_mem_disjSum.mp hi) (inr_mem_disjSum.mp hj) (fun he=> hn (congr_arg _ he))
   unfold harvest; rw [he,toLeft_disjSum]; unfold pole ahead obscures valueP
   by_cases hv: separated (blocked p) v∧ v.biUnion d=W; swap; · rw [if_neg (fun h=> hv ⟨h.1.1,h.2⟩),if_neg hv,zero_mul]
   by_cases hs:separated (blocked q) s; swap; · rw [if_neg (fun h=> hs h.1.2.1),if_neg hs,mul_zero]
   rw [if_pos hv,if_pos hs]; by_cases hp:∀ i∈s,Disjoint (v.biUnion p) (q i)
   · rw [if_pos ⟨⟨hv.1,hs,hp⟩,hv.2⟩,prod_disjSum]; exact congr_arg ((∏ i∈v,u i)*·) (Finset.prod_congr rfl fun i hi=> (show omission q g _ i=_ from if_pos (hp i hi)).symm)
   rw [if_neg (fun h=> hp h.1.2.2)]; push Not at hp; obtain ⟨i,hi,hp⟩:=hp; rw [prod_eq_zero hi (show omission q g _ i=0 from if_neg hp),mul_zero]
def packEquiv (ι κ :Type*) : Finset ι× Finset κ≃ Finset (ι⊕κ):={ toFun:=fun s=> s.1.disjSum s.2, invFun:= fun s=>(s.toLeft,s.toRight), left_inv s:=Prod.ext (toLeft_disjSum ..) (toRight_disjSum ..),right_inv s:=by ext x; cases x<;> simp }
-- packEquiv def (should be def, replace)
variable {a c t r:ℝ}{G:κ→ℝ}{B:ℕ}
variable (hp :∀ i,d i ⊆ p i)(hq :∀ i,(q i).Nonempty)(h:Trees.Ready q B G a c t r)(ha:0≤a)(hv:∀ i, ‖g i‖≤ G i)
include hq h ha hv
open scoped Classical
lemma plow (v:X):
   Summable (pole p d q W u g v) ∧ ∑' i,pole p d q W u g v i = NormedSpace.exp (scaleU q g)*(∑ i:Finset (Support n), tableP p d q W u g (v.disjSum i)):=by
   let p':= v.biUnion p; let Z:= omission q g p'
   obtain ⟨h1,h2,h3,h4⟩:= portage (w:=g) (p:=q) hq h hv ha p'
   refine ⟨h3.mul_left _,?_⟩
   unfold pole; rw [h3.tsum_mul_left,← show NormedSpace.exp (scaleU q g)*_=∑' s,valueP (blocked q) (_) s from h4, mul_left_comm]; apply congr_arg
   unfold ahead; split
   next hx =>
     have hv:Summable (fun i=>‖termP (blocked q) g i‖):= (absoluteS (blocked q) g q B (literal_test q hq) hq ha (foyer (fun _=>norm_nonneg _) h hv)).2.1
     rw [← GasP.departures p' hv] -- sig
     simp_rw [← Finset.sum_neg_distrib]
     let E := (univ:Finset (Support n)).filter (fun i=>¬Disjoint p' i)
     let y (i:Support n):= -(portion q g i)
     have he : ∑ T: Support n, -(if Disjoint p' T then (0:K) else portion q g T)=∑ i∈E,y i :=by
         rw [sum_filter]; apply sum_congr rfl; intro i _; split_ifs <;> simp [y]
     rw [he, exp_sum]; have hg (i:Support n): exp (y i) = dropsP q g i+ 1:=(sub_add_cancel ..).symm
     simp_rw [hg, Finset.prod_add_one] -- signature
     rw [Finset.mul_sum]; -- extra terms
     symm; refine (Finset.sum_subset (Finset.subset_univ E.powerset) ?_).symm.trans (Finset.sum_congr rfl (fun i hi=>?_))
     · intro i hi hh; unfold tableP; rw [if_neg]; intro ht; apply hh; rw [toLeft_disjSum,toRight_disjSum] at ht; exact mem_powerset.mpr (fun j hj=>mem_filter.mpr ⟨mem_univ _,ht.2 j hj⟩)
     unfold tableP; rw [toLeft_disjSum,toRight_disjSum,if_pos,prod_disjSum]; rotate_left; · exact ⟨hx,fun j hj=>(mem_filter.mp (mem_powerset.mp hi hj)).2⟩
     rfl
   next hx=> rw [zero_mul]; symm; refine Finset.sum_eq_zero fun i _=>?_ ; unfold tableP; rw [toLeft_disjSum]; exact if_neg (fun ht=>hx ht.1)
omit hq h ha hv
lemma fullR {A:ℝ}(h:SumBudget (fun i=> ‖u i‖) A): Summable (tableP p d q W u g):=by
   let m (i:J):= ‖samples q u g i‖; have hm: Summable m:= Summable.sum (f:=m) h.2.1 (hasSum_fintype _).summable -- edit
   refine Summable.of_norm (Summable.of_nonneg_of_le (fun i=>norm_nonneg _) ?_ (Product.set_products (show SumBudget m _ from ⟨fun _=>norm_nonneg _,hm,(le_refl (∑' i,m i))⟩)).2.1)
   intro i; unfold tableP; split; exact norm_prod_le ..; rw [norm_zero]; exact prod_nonneg fun _ _=> norm_nonneg _
include hq h ha hv hp
theorem exact_march {A: ℝ}(ht:SumBudget (fun i=>‖u i‖) A) :
   let Z:= harvest p d q W u g
   let V:= ward p d q W u g
   Summable Z ∧ Summable V ∧ (∑' v,Z v)=NormedSpace.exp (scaleU q g) * ∑' i,V i:=by
    intro Z Y
    let T:= tableP p d q W u g
    have hT:Summable T:=fullR p d q W u g ht
    let P i:= Ac.Parts (facesP p) i
    have hP: Injective P:=fun i j h=> by rw [← Ac.reconstruct (facesP p) i,← Ac.reconstruct (facesP p) j,show Ac.Parts (facesP p) i=Ac.Parts (facesP p) j from h]
    have hvZ i:P i = P i:=rfl
    have hY i: Y (P i)=T i:=by
       have hs : (P i).biUnion id=i :=Ac.reconstruct ..
       by_cases hx : wide p (P i)
       · exact Eq.symm (by simpa only [hs] using! resumes q W u g hp (P i) hx)
       unfold Y T; unfold ward; rw [if_neg (fun h=> hx h.1)]; symm; refine if_neg ?_; rintro ⟨⟨he,hh⟩,hv⟩; exact hx (seated i he hv)
    have hz : HasSum Y (∑' i,T i):= by
       refine (hP.hasSum_iff (f:=Y) ?_).mp ?sum
       · intro i hn; refine if_neg ?_; intro h; exact hn ⟨i.biUnion id, Ac.separates _ _ (fun j hj=>(h.1.1 j hj).2.1) h.1.2⟩
       case sum=> change HasSum (Y ∘ P) _; rw [show Y ∘ P=T from funext hY]; exact hT.hasSum
    have hx1 : Summable fun i:κ=> ‖g i‖:=by
       have ha': 0≤ a+t:=add_nonneg ha h.2.1.le; have he:= Product.everyone_ne q B (fun i=> norm_nonneg (g i)) (fun i _=>hq i) (foyer (fun _=>norm_nonneg _) h hv).2.2.2.2.2
       refine he.2.1.of_nonneg_of_le (fun _=> norm_nonneg _) fun i=> le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg ha' (Nat.cast_nonneg _)))
    have hw:Summable fun i:ι⊕κ => ‖Sum.elim u g i‖ := Summable.sum (f:=fun i=> ‖Sum.elim u g i‖) ht.2.1 hx1
    let W₁ i:= ‖Sum.elim u g i‖
    have hZ: Summable Z:= by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun _=>norm_nonneg _) ?_ (Product.set_products (show SumBudget W₁ _ from ⟨fun _=> norm_nonneg _,hw,le_refl _⟩)).2.1)
      intro i; unfold Z harvest; split; exact norm_prod_le ..; rw [norm_zero]; exact prod_nonneg fun _ _=>norm_nonneg _
    refine ⟨hZ,hz.summable,?_⟩
    rw [hz.tsum_eq, ← Equiv.tsum_eq (packEquiv ι κ), ← Equiv.tsum_eq (packEquiv ι (Support n))] -- sig
    have he := (hZ.comp_injective (packEquiv ι κ).injective); have hh := hT.comp_injective (packEquiv ι (Support n)).injective
    erw [he.tsum_prod,hh.tsum_prod,← (hh.prod).tsum_mul_left]
    refine tsum_congr fun i=>?_
    change (∑' k, Z (i.disjSum k))=NormedSpace.exp _ *∑' k:Finset (Support n), T (i.disjSum k)
    unfold Z; simp_rw [GasP.allies]; rw [(plow p d q W u g hq h ha hv i).2,tsum_fintype]
end YM.QCD.GasP
