import YM.Play.Bole
import YM.MassiveQCD.Cupola.Crown
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace Cupola Ribbon QCD.Bera QCD.Anomaly
open MeasureTheory BigOperators
open scoped Topology BigOperators ContDiff Classical
variable {I A: Type}{B:Type*}
local notation "H"=> Finset I
namespace Chamber
-- Mark support dictionary and inverse cumulant.
-- disjoint products at exact marker grade. Universe in stance.
def registry (v:H):Finset (Finset H):= v.powerset.powerset.filter (fun i:Finset H=> ∅∉i ∧ i.biUnion id=v∧ (i:Set H).PairwiseDisjoint id)
-- intentionally no tag=[] when v≠∅.
def parties [CommSemiring B](f:Finset I→ B)(v: Finset I) := ∑ i ∈ registry v,∏ j∈i,f j
def cut (v: Finset I) := (registry v).erase {v}
lemma member {D:Finset H}{v:H}(h:D∈registry v){i:H}(hp:i∈D): i.Nonempty∧ i⊆v:=by
    obtain ⟨hx,h,hD,h₃⟩:=mem_filter.mp h; exact ⟨Finset.nonempty_iff_ne_empty.mpr (fun h₃=> h (h₃ ▸ hp)),mem_powerset.mp (mem_powerset.mp hx hp)⟩
lemma native {v:H}(h:v.Nonempty): {v}∈ registry v:=mem_filter.mpr ⟨mem_powerset.mpr (singleton_subset_iff.mpr (mem_powerset_self _)),fun h'=> h.ne_empty (mem_singleton.mp h').symm,by simp,by simp⟩
lemma hollow [CommSemiring B](f:H→ B) : parties f ∅=1:=by
   unfold parties; rw [show registry (∅:H)={∅} from ?_,sum_singleton,prod_empty]; ext i; constructor
   · intro h; apply mem_singleton.mpr; by_contra hx; obtain ⟨j,hj⟩:= nonempty_iff_ne_empty.mpr hx; obtain ⟨hv,hT⟩:= member h hj; exact hv.ne_empty (subset_empty.mp hT)
   intro h; rw [mem_singleton.mp h]; exact mem_filter.mpr ⟨by simp,by simp⟩
lemma useful [CommSemiring B](f:H→ B){v:H}(h:v.Nonempty): parties f v =f v +∑ i∈cut v,∏ j∈i,f j:=by unfold parties; symm; exact Eq.trans (congrArg (·+_) (prod_singleton f v|>.symm)) (add_sum_erase _ (fun i:Finset H=> ∏ j∈i,f j) (native h)) -- arg
lemma limit {v:H} {i:Finset H} (h:i∈ cut v){j:H}(hj:j∈i): j⊂ v:=by
    obtain ⟨hx,hT⟩:=mem_erase.mp h; obtain ⟨_,hv,hq,hZ⟩:=mem_filter.mp hT; apply lt_of_le_of_ne (member hT hj).2; intro hh; subst j
    apply hx; refine (eq_singleton_iff_unique_mem.mpr ⟨hj,?_⟩); intro k hk; by_contra hh; have ht:Disjoint k v:=hZ hk hj hh; obtain ⟨ha,hH⟩:=member hT hk; obtain ⟨x,hx⟩:=ha; exact Finset.disjoint_left.mp ht hx (hH hx)
section
variable [Fintype I][Fintype A]
abbrev VaultP (A:Type)[Fintype A](q:I→Bool)(v: Finset I) : Submodule ℂ (Patio (A⊕Spine I)):=Submodule.comap (light _).toLinearMap (LinearMap.range (stake A (burst q v)).toLinearMap)
-- Data measures all support restrictions.Header.Tilt.
end
section
variable [CommRing B]
variable (f:Finset I→B)
-- Avoid `termination_by`
def sturdy : ℕ→ (H→ B)
 | 0,_=>0
 | n+1,i=> if i.Nonempty then f i-∑ j∈cut i, ∏ k∈ j, sturdy n k else 0
-- κ output log nonempty.Power radii not yet.
def cetacea (v:Finset I) := sturdy f v.card v -- n for v
lemma stout (n:ℕ)(i:H)(he:i.card≤n): sturdy f (n+1) i= sturdy f n i:=by
   induction n generalizing i with
   | zero=> have hs: i=∅:=Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero he); simp [hs,sturdy]
   | succ k ih=>
      by_cases hp:i.Nonempty; · rw [sturdy,if_pos hp,sturdy]; rw [if_pos hp]; apply congr_arg; refine sum_congr rfl fun j hj=> prod_congr rfl fun i' hi'=> ?_; apply ih; have h:=Finset.card_lt_card (limit hj hi'); omega
      simp [sturdy,hp]
lemma pass (i:H)(n:ℕ)(h:i.card≤n): sturdy f n i=cetacea f i :=by
    induction n,h using Nat.le_induction with| base=>rfl| succ n h ih=>exact Eq.trans (stout f _ _ h) ih
lemma cet (i:H): cetacea f i= if i.Nonempty then f i-∑ j∈cut i,∏ k∈j,cetacea f k else 0 :=by
   rw [← pass f i (i.card+1) (by omega),sturdy]; split; next hp=> apply congr_arg; exact sum_congr rfl fun j hj=> prod_congr rfl fun k hk=> pass _ _ _ (Finset.card_lt_card (limit hj hk)).le
   rfl
lemma carries (v:H)(h:f ∅=1): parties (cetacea f) v=f v:=by
   rcases v.eq_empty_or_nonempty with ha|ha; · rw [ha,h,hollow]
   rw [useful _ ha,cet f v,if_pos ha]; abel
lemma only (g:H→ B) (X:H) (h:∀ v⊆X,parties g v=f v)(hs:g ∅=0):∀ v⊆X,g v=cetacea f v:=by
   suffices he:∀ n:ℕ,∀ v⊆X,v.card=n → g v=cetacea f v from fun i hi=> he _ _ hi rfl
   intro i; induction i using Nat.strong_induction_on with
   | h i ih=>
      intro v hv he; rcases v.eq_empty_or_nonempty with ha|ha; · rw [ha,hs,cet]; simp
      rw [cet f v,if_pos ha,← h v hv,useful g ha]; have hp j(h:j∈cut v): ∏ i∈j,cetacea f i=∏ i∈j,g i:= prod_congr rfl fun i hi=> (ih _ ((Finset.card_lt_card (limit h hi)).trans_le he.le) i ((member (mem_of_mem_erase h) hi).2.trans hv) rfl).symm; rw [sum_congr rfl hp]; abel -- shadow
end
lemma patrons {v:H} {i:Finset H} (hi:i∈registry v) : ∑ s∈i,s.card=v.card := by
    obtain ⟨_,_,he,hx⟩:=mem_filter.mp hi; rw [← he,card_biUnion hx]; rfl
-- general product norm.L
section
variable [CommSemiring B](f:Finset I→B) (X:Finset I)
lemma signal (h:∀ i∈ X.powerset,∀ j∈X.powerset,¬ Disjoint i j → f i*f j=0) :
    (∏ i∈ X.powerset.erase ∅, (1+f i))=∑ i∈ X.powerset,parties f i:=by
    let P:= X.powerset.erase (∅:H); let W:=P.powerset; let A:=W.filter (fun s:Finset H=>(s:Set H).PairwiseDisjoint id); let F i:=∏ j∈i,f j
    have hx:(∏ i∈P, (1+f i))=∑ s ∈ W,F s:=by
       rw [Finset.prod_congr rfl (g:=fun i=> f i+1) (fun _ _=> add_comm ..), Finset.prod_add]; simp only [one_mul,prod_const_one,mul_one]; rfl
    rw [hx]; have ht(i:H)(hi:i⊆X): registry i=A.filter (fun s=>s.biUnion id=i):=by
        ext p; simp only [A,W,registry,mem_filter,mem_powerset]; constructor
        · rintro ⟨hp,hE,hq,hQ⟩; refine ⟨⟨(?_),hQ⟩,hq⟩; intro j hj; exact mem_erase.mpr ⟨fun eq=> hE (eq ▸ hj),mem_powerset.mpr ((mem_powerset.mp (hp hj)).trans hi)⟩
        rintro ⟨⟨hp,hq⟩,hQ⟩; refine ⟨(?_),fun hx=> notMem_erase _ _ (hp hx),hQ,hq⟩; intro j hj; apply mem_powerset.mpr; rw [← hQ]; exact subset_biUnion_of_mem id hj
    have hp (s:Finset H)(hs:s∈A): s.biUnion id ∈ X.powerset:=by
       apply mem_powerset.mpr; intro j hj; obtain ⟨k,hk,hj⟩:=mem_biUnion.mp hj; exact mem_powerset.mp (mem_of_mem_erase (mem_powerset.mp ((mem_filter.mp hs).1) hk)) hj
    have hg : ∑ i∈X.powerset,parties f i=∑ i∈ A,F i:=by
       rw [← Finset.sum_fiberwise_of_maps_to hp F]; refine sum_congr rfl fun i hi=>?_; unfold parties; rw [ht i (mem_powerset.mp hi)] -- implicit result.T.
    rw [hg]; symm; apply sum_subset (filter_subset ..); intro i hi hx; unfold A at hx; simp only [mem_filter,hi,true_and] at hx; simp only [Set.PairwiseDisjoint, Set.Pairwise] at hx; push Not at hx; obtain ⟨b,hb,c,hc,hn,hz⟩:=hx
    unfold F; rw [← mul_prod_erase i f hc,← Finset.mul_prod_erase _ f (Finset.mem_erase.mpr ⟨hn,hb⟩), ← mul_assoc,h c (mem_of_mem_erase (mem_powerset.mp hi hc)) b (mem_of_mem_erase (mem_powerset.mp hi hb)) (fun h=>hz h.symm),zero_mul]
end
end Chamber
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Chamber.only
#print axioms YM.MassiveQCD.Play.Chamber.signal
