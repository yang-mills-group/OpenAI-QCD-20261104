import YM.QCD.Creek.Flags
import YM.QCD.Cove.Lid
/-! # graded maps with degree-price budgets (no argument from large-type-card)
   Board record addresses in a set U, doesn't carry gauge stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Anomaly
open Cove Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B: Type*}[Fintype A][Fintype B]{P Q X U V:Finset A}{A' :Finset B}{n m i:ℕ}
-- support & degree one.
def Rim (s: Finset A)(n:ℕ) : Submodule ℂ (Alg A) where
  carrier := {x | ∀ i,coef i x ≠ 0 → i⊆s ∧ i.card≤n}
  smul_mem' := by
    intro r x h i hi; exact h i fun he=> hi (by rw [map_smul,he,smul_zero])
  add_mem' := by
    intro x y h g i hi; by_cases hh: coef i x ≠0; exact h i hh
    exact g i (fun he=> hi (by simp [not_not.mp hh,he]))
  zero_mem' := fun i hi=> (hi (map_zero _)).elim
namespace Rim
variable {s s':Finset A}{a:A}
lemma rimIn {x:Alg A}(h:x∈Rim s' n)(i) (hi:coef i x≠0) :i⊆s' ∧ i.card≤n:= h i hi -- s implicit?
lemma monotone (h:U⊆V)(hp:n≤m): Rim U n ≤ Rim V m :=fun _ hx i hi=> ⟨(rimIn hx i hi).1.trans h,(rimIn hx i hi).2.trans hp⟩
lemma layerIn (hx:s⊆ U)(hp:s.card≤n): mono s∈ Rim U n:=by
   intro i hi; have h:i=s:=by_contra fun h=>hi (read_other _ _ h); exact h.symm ▸ (⟨hx,hp⟩:s⊆U ∧ _)
lemma record {x:Alg A}(h:x∈Rim U n): x=∑ i∈U.powerset.filter (fun i=> i.card≤n), coef i x • mono i:=by
   calc
    _ = ∑ i:Finset A,coef i x • mono i:=(write x).symm
    _ = _ := (sum_subset (subset_univ _) (fun i _ hi=> by rw [show coef i x=0 from by_contra (fun hz=> hi (mem_filter.mpr ⟨mem_powerset.mpr (rimIn h i hz).1,(rimIn h i hz).2⟩)),zero_smul])).symm
-- rim support via embeds.Halo.
lemma monoIn (P:Finset A): mono P∈region P := by
    obtain ⟨g,-,ht,hh⟩:=expression P; rw [hh]; let i(k): P:=⟨g k,(ht _).2 ⟨k,rfl⟩⟩; let p (j:↥P):A:=j
    refine ⟨(List.ofFn (atom ∘ i)).prod,?_⟩; change embed p _=_; rw [map_list_prod,List.map_ofFn]; congr 1; apply congr_arg; funext j; exact embed_atom ..
lemma affects {x:Alg A}(h:x∈Rim U n): x∈region U:=by
   have ht:= Rim.record h; rw [ht]
   exact Subalgebra.sum_mem _ fun i hi=> Subalgebra.smul_mem _ (Creek.regionMon (mem_powerset.mp (mem_filter.mp hi).1) (monoIn i)) _
lemma whenever (x: Alg A)(h:x∈region U) {i:Finset A}(he:coef i x≠0): i⊆U:=by
   obtain ⟨k,rfl⟩:=h; let f:↥U ↪ A:= ⟨Subtype.val,Subtype.val_injective⟩; by_contra hn
   apply he; change coef i (embed f k)=0; rw [← write k,map_sum,map_sum]; apply sum_eq_zero; intro j _; simp only [map_smul]; have h:i ≠ j.map f:=by
        intro he; apply hn; rw [he]; intro b hb; obtain ⟨b',_,rfl⟩:= mem_map.mp hb; exact b'.property
   rcases embed_blade f j with hx|hx<;>change _ • coef i (embed f (mono j))=0<;>rw [hx] <;> simp [read_other _ _ h]
lemma bound (x: Alg A)(h:x∈layer A n)(hr:x∈ region U): x∈ Rim U n:=by
   intro i hi; exact ⟨whenever x hr hi, (show i.card=n from by_contra fun hz=> hi (spectrum h _ hz)).le⟩
-- grade calculus
lemma one (U:Finset A): (1: Alg A) ∈ Rim U n:= mono_empty (A:=A) ▸ layerIn (empty_subset U) (by simp)
lemma atoms (hx:a∈U): atom a∈Rim U 1:= by rw [← mono_single]; exact layerIn (singleton_subset_iff.mpr hx) (card_singleton ..|>.le)
lemma multiply {x y:Alg A}(h:x∈Rim U n)(g:y∈Rim U m): x*y∈Rim U (n+m):=by
    rw [record h, record g]; simp_rw [sum_mul,mul_sum]; refine Submodule.sum_mem _ fun i hi=>Submodule.sum_mem _ fun j hj=>?_; obtain ⟨hi,hv⟩:=mem_filter.mp hi; obtain ⟨hj,he⟩:=mem_filter.mp hj
    let a:= coef i x • mono i; let b:=coef j y •mono j; have hp:=layer_mul (show a∈layer A i.card from Submodule.smul_mem _ _ (homogeneous i)) (show b∈layer A j.card from Submodule.smul_mem _ _ (homogeneous j))
    have hs:a*b∈Rim U (i.card+j.card):= bound _ hp (Subalgebra.mul_mem (region U) (affects (x:=a) (n:=n) ((Rim U n).smul_mem _ (layerIn (mem_powerset.mp hi) hv))) (affects (n:=m) ((Rim U m).smul_mem _ (layerIn (mem_powerset.mp hj) he))))
    exact monotone (Subset.refl _) (add_le_add hv he) hs
lemma clip (a:A){x:Alg A}(h:x∈ Rim U n): v a x∈ Rim U (n-1):=by
   rw [record h,map_sum]; refine Submodule.sum_mem _ fun i hi=> ?_; obtain ⟨hs,hp⟩:=mem_filter.mp hi; rw [map_smul]; exact Submodule.smul_mem _ _ (monotone (mem_powerset.mp hs) (Nat.sub_le_sub_right hp _) (bound _ (lowers a _) (show v a (mono i)∈ _ from preserves _ (monoIn i))))
lemma vacated (a:A){x:Alg A}(h:x∈ Rim U 0): v a x=0:=by
   rw [record h,map_sum]; apply sum_eq_zero; intro i hi; have hh:i=∅:=card_eq_zero.mp (Nat.eq_zero_of_le_zero (mem_filter.mp hi).2); rw [map_smul, hh,mono_empty,show v a 1=0 from vary_one ..,smul_zero]
lemma patched (M: Matrix A B ℂ)(h:∀ i∈U,∀ j,M i j ≠0 → j∈ A'){x:Alg A}(hf:x∈Rim U n): changeVars M x∈Rim A' n:=by
   rw [record hf,map_sum]; refine Submodule.sum_mem _ fun i hi=> ?_; rw [map_smul]; apply Submodule.smul_mem; refine monotone (Finset.Subset.refl _) (mem_filter.mp hi).2 (bound _ (exterior_layer _ (homogeneous i)) (?_)); apply effects (changeVars M) _ (mono i) (monoIn i); intro j hj; rw [change_atom]; apply Subalgebra.sum_mem; intro k hk; by_cases hk:M j k=0; · rw [hk,zero_smul]; exact Subalgebra.zero_mem _
   exact Subalgebra.smul_mem _ (marked k A' (h _ (mem_powerset.mp (mem_filter.mp hi).1 hj) _ hk)) _
end Rim
end YM.QCD.Anomaly
#print axioms YM.QCD.Anomaly.Rim.multiply
#print axioms YM.QCD.Anomaly.Rim.clip
