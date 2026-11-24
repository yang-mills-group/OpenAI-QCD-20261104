import YM.QCD.Cove.Crew

/-!
# Tensor algebra of rooted super-markers at cells
 Keep all actual old Graded variables. Markers on the RIGHT, coefficient operations
 on spin involve NO dependent sign because of this and every transmission preserving parity.
 But readers can be odd, and Gram estimates later must keep full ordering signs. We'll
 embed this storage algebra (or its even elements) before budgeting (in an N-universal
 alphabet with no estimate depending on marker count), see later. `scrape` is extraction
 spending only on prices of actually included symbols.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Ribbon
open QCD QCD.Grass QCD.Cove QCD.Creek
open Filter Function Finset NormedSpace MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {A B C D:Type} [Fintype A][Fintype B][Fintype C]
-- `Leaf A` (not QCD.Leaf). use later. here I any blades (no parity restriction).
variable (B)
noncomputable abbrev fiber : Alg A →ₐ[ℂ] Alg (A⊕B):=embed Sum.inl
variable (A)
variable {B}
noncomputable abbrev quill : Alg B→ₐ[ℂ] Alg (A⊕B):=embed Sum.inr
noncomputable def stake (i:Finset B): Alg A →L[ℂ] Alg (A⊕B):=LinearMap.toContinuousLinearMap ((LinearMap.mulRight ℂ (quill A (mono i))).comp (fiber B).toLinearMap)
lemma markedOut (s:Finset B)(x: Alg A): stake A s x=fiber B x *quill A (mono s):=rfl
lemma quiet (x: Alg A): stake A (∅:Finset B) x= fiber B x:= by rw [markedOut,mono_empty,map_one,mul_one]
variable {A}
lemma broken (s:Finset A)(i:Finset B): stake A i (mono s)=mono (s.disjSum i) ∨ stake A i (mono s)=-mono (s.disjSum i):=by
   let f:A↪ A⊕B:= Embedding.inl; let g:B↪ A⊕B:= Embedding.inr; have ht: (s.disjSum i)=s.map f ∪ i.map g:=by ext y; cases y <;> simp [f,g]
   have hp: Disjoint (s.map f) (i.map g):=Finset.disjoint_left.mpr (by rintro (j|j) hv hw <;> simp_all [f,g])
   have h:= mono_mul_sign _ _ hp; rw [Finset.disjUnion_eq_union,← ht] at h
   rcases embed_blade f s with he|he <;> rcases embed_blade g i with hg|hg <;> change embed f _ * embed g _=_ ∨ embed f _ *embed g _=_ <;> rw [he,hg] <;> rcases h with h|h <;> simp [neg_mul,mul_neg,h]
omit [Fintype A] [Fintype B] in
lemma ribbon_inj {s t:Finset A}{i j:Finset B}(h:s.disjSum i=t.disjSum j):s=t ∧ i=j:=⟨by simpa using congr_arg Finset.toLeft h,by simpa using congr_arg Finset.toRight h⟩
variable (A)
noncomputable def scrape (s:Finset B): Alg (A⊕B)→L[ℂ] Alg A:=
   ∑ i: Finset A, (LinearMap.toContinuousLinearMap (coef (i.disjSum s))).smulRight (coef (i.disjSum s) (stake A s (mono i)) • mono i)
lemma pokes (i:Finset B)(x: Alg (A⊕B)): scrape A i x=∑ s:Finset A,coef (s.disjSum i) x • (coef (s.disjSum i) (stake A i (mono s)) • mono s):=by unfold scrape; rw [_root_.sum_apply]; rfl
lemma stakes (s:Finset A) (i j:Finset B): scrape A i (stake A j (mono s))=if i=j then mono s else 0:=by
   rw [pokes]; split
   · subst i; rw [sum_eq_single s]
     · rcases broken s j with h|h <;> rw [h] <;> simp
     · intro k _ hk; rcases broken s j with h|h <;> simp only [h,map_neg,read_other _ _ (show k.disjSum j ≠ s.disjSum j from fun h↦ hk (ribbon_inj h).1),neg_zero,zero_smul]
     simp
   next h=>
    refine sum_eq_zero (fun k _=>?_); rcases broken s j with he|he <;> rw [he] <;> simp [read_other _ _ (show k.disjSum i≠s.disjSum j from fun he=>h (ribbon_inj he).2)]
lemma stakesX (i j:Finset B)(x:Alg A): scrape A i (stake A j x)=if i=j then x else 0:=by
   conv_lhs=> rw [← write x,map_sum,map_sum]
   simp_rw [map_smul,stakes]; split_ifs with h <;> simp [write]
lemma quid (s:Finset B) (x:Alg A): scrape A s (stake A s x)=x:=by rw [stakesX,if_pos rfl]
noncomputable def restore (p:Finset B→Alg A) := ∑ i, stake A i (p i)
lemma rewriteR (x:Alg (A⊕B)): ∑ i: Finset B, stake A i (scrape A i x)=x:=by
   have h(s:Finset (A⊕B)): ∃ (i:Finset B)(y:Alg A), stake A i y=mono s:=by
      rcases broken s.toLeft s.toRight with h|h
      · exact ⟨_,_,h.trans (congr_arg _ (show s.toLeft.disjSum s.toRight=s by ext i; cases i <;> simp))⟩
      refine ⟨s.toRight,-mono s.toLeft,?_⟩; rw [map_neg,h,neg_neg, show s.toLeft.disjSum s.toRight=s by ext i; cases i <;>simp]
   have hv i: ∑ s:Finset B, stake A s (scrape A s (mono i))=mono i:=by
      obtain ⟨t,Y,HY⟩:=h i; rw [← HY,sum_eq_single t]
      · rw [quid]
      · intro j _ hj; rw [stakesX,if_neg hj,map_zero]
      simp
   conv_lhs=> rw [← write x]
   simp_rw [map_sum,map_smul]; rw [sum_comm]; simp_rw [← Finset.smul_sum,hv]; exact write x
lemma rewrites (x:Alg (A⊕B)): restore A (fun i=> scrape A i x)=x:=rewriteR A x
lemma wide (f:Finset B→Alg A)(t:Finset B): scrape A t (restore A f)= f t:=by
   unfold restore; rw [map_sum,sum_eq_single t]
   · exact quid ..
   · exact fun i _ hi=> by rw [stakesX,if_neg hi.symm]
   simp
lemma vista (x y:Alg (A⊕B)) (h:∀ i,scrape A i x=scrape A i y): x=y:=by
   rw [← rewriteR A x,← rewriteR A y]; simp_rw [h]
lemma sticker_add (x y:Alg A)(i:Finset B): fiber B x * stake A i y= stake A i (x*y):=by rw [markedOut,markedOut,← mul_assoc,map_mul]
end YM.MassiveQCD.Ribbon
