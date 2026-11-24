import YM.QCD.Nola.Summer
import YM.QCD.Gas.Ray
import YM.QCD.Gas.Pavilion
/-! # incident-radius charge logarithm -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef
open scoped BigOperators Classical Topology ContDiff
variable {ι K : Type*}[NormedCommRing K][NormOneClass K][NormedAlgebra ℝ K][NormedAlgebra ℚ K][CompleteSpace K]
variable {n : Side} {l k : ℕ}{X Y : Support n}
-- diameter always
noncomputable def reel (A: Support n):ℕ:= A.sup fun i=> A.sup fun j=> separation i j
lemma roofS {i j:Site n} (hi:i∈X)(hp:j∈X): separation i j ≤reel X := -- i j binder
     le_trans (le_sup (f:=fun j=> separation i j) hp) (le_sup (f:=fun i=> X.sup fun j=>separation i j) hi)
lemma roof (h:∀ i∈X,∀ j∈X,separation i j ≤ k):reel X ≤k:=Finset.sup_le fun i hi=> Finset.sup_le fun j hj=>h i hi j hj
lemma reel_mono (h:X⊆Y):reel X≤reel Y:= roof fun _ hi _ hj=> roofS (h hi) (h hj)
lemma dog {x: Site n} (hi:x∈X)(hh:x∈Y): reel (X∪Y)≤ reel X+reel Y:=by
    apply roof; intro i hp j hz; rcases mem_union.mp hp with hx|hx <;> rcases mem_union.mp hz with hz|hz
    · exact (roofS hx hz).trans (by omega)
    · exact (separation_triangle i x j).trans (Nat.add_le_add (roofS hx hi) (roofS hh hz))
    · rw [separation_comm]; exact (separation_triangle j x i).trans (Nat.add_le_add (roofS hz hi) (roofS hh hx))
    exact (roofS hx hz).trans (by omega)
def tell (X : Support n)(m:ℕ):ℝ:= (reel X+1:ℝ)^m
lemma tell_one (X : Support n)(m:ℕ) : 1 ≤ tell X m:= one_le_pow₀ (by change 1 ≤ (reel X:ℝ)+1; simp) -- positivity inequalities?
lemma tell_union {x:Site n}(hi:x∈X)(hz:x∈Y)(m:ℕ): tell (X∪Y) m ≤ tell X m*tell Y m:=by
      unfold tell; rw [← mul_pow]; gcongr; have he: (reel (X∪Y):ℝ) ≤ (reel X:ℝ)+ reel Y:=by exact_mod_cast dog hi hz
      linarith only [he,mul_nonneg (Nat.cast_nonneg (reel X)) (Nat.cast_nonneg (reel Y): (0:ℝ)≤_)] -- syntax
variable (p : ι → Support n)
lemma tarot (s: Finset ι)(hs:Ac.Spark p s)(m:ℕ):tell (s.biUnion p) m≤ ∏ i∈s,tell (p i) m:=by
  have h : ∀ k : ℕ, k+1≤ s.card → ∃ u⊆s,u.card=k+1 ∧ tell (u.biUnion p) m ≤ ∏ i∈u,tell (p i) m := by
    intro k; induction k with
    | zero =>
      intro _; obtain ⟨i,hi⟩ := hs.1; exact ⟨{i},by simp [hi],by simp,by simp⟩
    | succ k IH =>
      intro hh
      obtain ⟨u,h1,h2,h3⟩ := IH (by omega)
      obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<u.card by omega); obtain ⟨j,hj,hx⟩ := exists_mem_notMem_of_card_lt_card (show u.card<s.card by omega)
      have H : ∀ j, Ac.chain p s i j → j∉u → ∃ t∈s,t∉u ∧ Ac.meets p t (u.biUnion p) := by
        intro b hb; induction hb with
        | refl => exact fun H => absurd hi H
        | @tail a b _ ht I =>
          intro h; by_cases hn : a∈u
          · obtain ⟨q,hq,hp⟩ := ht.2.2; exact ⟨b,ht.2.1,h,q,mem_biUnion.mpr ⟨a,hn,hq⟩,hp⟩
          exact I hn
      obtain ⟨t,ht,hz,x,hp,hq⟩ := H j (hs.2 i (h1 hi) j hj) hx
      refine ⟨insert t u,insert_subset ht h1,by simp only [card_insert_of_notMem hz,h2],?_⟩
      rw [prod_insert hz,biUnion_insert]
      exact (tell_union hq hp m).trans (mul_le_mul_of_nonneg_left h3 (zero_le_one.trans (tell_one _ _)))
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_one.mpr (Finset.card_pos.mpr hs.1)
  obtain ⟨u,h1,h2,h3⟩ := h a ha.ge
  rwa [Finset.eq_of_subset_of_card_le h1 (ha ▸ h2.ge)] at h3
lemma ash {R:ι→ι→Prop} {m : ℕ} (z : Ursell.Tuple ι m) (ht: Tests R p)(he : coefficient R z ≠ 0) : Ac.Spark (p ∘ z) univ := by
  let T := pot R z
  have hg : (connectedGroups T).Nonempty := by
    by_contra hh; rw [not_nonempty_iff_eq_empty] at hh
    exact he (by change ∑ i∈connectedGroups T, alternating i=0; rw [hh,sum_empty])
  obtain ⟨s,hs⟩ := hg
  obtain ⟨hk,hs⟩ := belongs.mp hs
  obtain ⟨q,d,hp⟩ := Breadth.build (Graph.link s) (fun _ => 0) (hs none)
  have hh : Graph.sprouts T q := ⟨Breadth.growth_ranked hp.toGrowth,
    fun i => ⟨(hp.edges i).1,hk (hp.edges i).2⟩⟩
  let X:= Trees.installed p (p (z none)) (z ∘ some)
  have hu : p ∘ z=X:= funext (fun i=>by cases i <;> rfl)
  rw [hu]; exact ⟨⟨none,mem_univ _⟩,fun i _ j _=>ReflTransGen.trans (Ac.swaps X (rooted_paths p (spanned R p ht hh) i)) (rooted_paths p (spanned R p ht hh) j)⟩
end YM.QCD.Nola
