import YM.Play.Coins
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace Cupola Ribbon QCD.Bera QCD.Anomaly
open MeasureTheory BigOperators Matrix
open scoped Topology BigOperators ContDiff Classical
variable {I K A B G E: Type}[Fintype I][Fintype A][Fintype B][Fintype G][Fintype E]
namespace Chamber
local notation "H"=> Finset I
variable {X Y: Finset I}{n m l:ℕ}{s t v:ℝ}
local notation "FA"=> Papers G (Patio A)
local notation "FB"=> Papers E (Patio B)
local notation "Zi"=>Finset I
-- f support measured in projected raw centers (w⊂X -> monotone). Record grid per slot each *unit* sym Bool.
variable (f:Finset I→Papers G (Patio A)) (w:I→ Finset G) (a:I→Finset A)
variable (Xp:Matrix G E ℂ)(Q:YM.Next.Rank.Normal.Symmetric G)(M:Matrix A B ℂ)(P:Matrix A A ℂ)
def switch : Finset I →Papers E (Patio B) := cetacea (fun i=> shootsW Xp Q M P (parties f i))
variable (he:∀ i⊆ X,i.Nonempty → f i ∈ Ledger (i.biUnion a) (i.biUnion w) (i.card*n) (i.card*m))
lemma lowMark {p:H} (hp:p⊆X) (h: ∀ i⊆X,i.Nonempty→ f i∈Ledger (i.biUnion a) (i.biUnion w) (i.card*n) (i.card*m)) : parties f p ∈ Ledger (p.biUnion a) (p.biUnion w) (p.card*n) (p.card*m):=by
   let A:=p.biUnion a; let W:=p.biUnion w
   have hm i (hi:i⊆ p)(hz:i.Nonempty): f i∈ Ledger A W (i.card*n) (i.card*m):= leaguer (h i (hi.trans hp) hz) (Finset.biUnion_subset_biUnion_of_subset_left _ hi) (Finset.biUnion_subset_biUnion_of_subset_left _ hi) le_rfl le_rfl
   have hv (s:Finset H)(h:∀ j∈s,(f j)∈Ledger A W (j.card*n) (j.card*m)): (∏ j∈s,f j)∈ Ledger A W (∑ j∈s,j.card*n) (∑ j∈s,j.card*m):=by induction s using Finset.induction_on with
    | empty=> rw [prod_empty]; exact arrives _
    | insert i s hi ih=> rw [prod_insert hi,sum_insert hi,sum_insert hi]; exact harbored (h _ (mem_insert_self ..)) (ih fun j hj=>h _ (mem_insert_of_mem hj))
   refine Submodule.sum_mem _ fun i hi=>?_ ; have hl:= hv i (fun j hj=>hm j (member hi hj).2 (member hi hj).1); rwa [← Finset.sum_mul,← Finset.sum_mul,patrons hi] at hl
variable (b:I→Finset E)(b':I→Finset B)
local notation "dawn"=> shootsW Xp Q M P
local notation "Qy"=> switch f Xp Q M P
include he
lemma move (hX:∀ i∈ X,∀ j∈ w i,∀ k,Xp j k ≠0→ k∈ b i)(hV:∀ i∈ X,∀ j∈a i,∀ k, M j k ≠0→ k∈ b' i) : Qy X∈ Ledger (X.biUnion b') (X.biUnion b) (X.card*n) (X.card*m):=by
    have hp i (hi:i⊆ X): dawn (parties f i)∈ Ledger (i.biUnion b') (i.biUnion b) (i.card*n) (i.card*m):=by
        refine types _ _ _ _ (lowMark f w a hi he) (?_) (?_)
        · intro j hj k hk; obtain ⟨m,hm,hj⟩:=mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨m,hm,hX m (hi hm) j hj k hk⟩
        intro j hj k hk; obtain ⟨m,hm,hj⟩:=mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨m,hm,hV m (hi hm) j hj k hk⟩
    suffices he : ∀ l:ℕ,∀ i⊆X,i.card=l → Qy i∈ Ledger (i.biUnion b') (i.biUnion b) (i.card*n) (i.card*m) from he _ _ (Subset.refl _) rfl
    intro l; induction l using Nat.strong_induction_on with
    | h l ih=> intro i hi hL; let D:=i.biUnion b'; let W:=i.biUnion b; unfold switch; rw [cet]; split; swap; · exact Submodule.zero_mem _
               refine Submodule.sub_mem _ (hp i hi) (Submodule.sum_mem _ fun j hj=>?_); have hx k (hk:k∈j): Qy k∈ Ledger D W (k.card*n) (k.card*m):=by
                      have h₀:= limit hj hk; exact leaguer (ih _ ((card_lt_card h₀).trans_le hL.le) _ (h₀.le.trans hi) rfl) (Finset.biUnion_subset_biUnion_of_subset_left _ h₀.le) (Finset.biUnion_subset_biUnion_of_subset_left _ h₀.le) le_rfl le_rfl
               have he v (hv:v⊆ j): (∏ i∈v,Qy i)∈ Ledger D W (∑ i∈v,i.card*n) (∑ i∈v,i.card*m):=by induction v using Finset.induction_on with
                | empty=> rw [prod_empty]; exact arrives _
                | insert p v h hx'=> rw [prod_insert h,sum_insert h,sum_insert h]; exact harbored (hx _ (hv (mem_insert_self ..))) (hx' ((subset_insert ..).trans hv))
               have h:= he j (Subset.refl j); rwa [←sum_mul,←sum_mul, patrons (mem_of_mem_erase hj)] at h
-- span law.Pow. porch far split. hypotheses postage geometry w.Marker centers
open Lattice Wilson
variable {c:Side}
lemma cutoff (z:I→Support c)(hz:∀ i⊆X,i.Nonempty →f i≠0 → Ac.Spark z i)
   (h:∀ i∈ X,∀ j∈ X, i ≠ j → Disjoint (z i) (z j)→ Disjoint (a i) (a j) ∧(∀ k∈ a i,∀ k'∈a j,P k k'=0∧P k' k=0) ∧(∀ k∈ w i,∀ k'∈ w j,Q.cov k k'=0)) (hk:Qy X≠0): Ac.Spark z X :=by
    by_contra hx
    apply hk; rcases X.eq_empty_or_nonempty with hW|hW; · unfold switch; rw [cet]; exact if_neg (by simp [hW])
    obtain ⟨i,hi⟩:=hW; let A0:= Ac.burst z X i; have ha:i∈A0:=(Ac.bright ..).2 ⟨hi,Relation.ReflTransGen.refl⟩; let B:=X\A0
    have hA: A0⊆ X:=fun _ h=> ((Ac.bright _ _ _).1 h).1
    have hG:Disjoint A0 B:=disjoint_sdiff
    have hs:¬ X⊆A0:=by
         intro h; apply hx; have hp: A0=X:= Subset.antisymm hA h; exact hp ▸ (Ac.burning z X i hi)
    have hw k (hk:k∈ A0) l (hl:l∈ B): Disjoint (z k) (z l):=by
        refine Finset.disjoint_left.mpr (fun b h1 h2=>?_); obtain ⟨h,h₀⟩:=mem_sdiff.mp hl; exact h₀ ((Ac.bright z _ _).2 ⟨h, Relation.ReflTransGen.tail ((Ac.bright ..).1 hk).2 ⟨hA hk,h,b,h1,h2⟩⟩)
    have hF {v:H}(hv:v⊆ X)(h₁:¬v⊆ A0)(h₂:¬v⊆B): f v=0:=by
       obtain ⟨j,hj,hJ⟩:=Finset.not_subset.mp h₁; obtain ⟨k,hk,hk'⟩:=Finset.not_subset.mp h₂; by_contra he; apply hJ; have hs: k∈ A0:=by_contra fun ht=>hk' (mem_sdiff.mpr ⟨hv hk,ht⟩)
       apply (Ac.bright ..).2; exact ⟨hv hj,Relation.ReflTransGen.trans ((Ac.bright ..).1 hs).2 (Relation.ReflTransGen.mono (p:=Ac.bonds z X) (fun a b h=> ⟨hv h.1,hv h.2.1,h.2.2⟩) _ _ ((hz v hv ⟨_,hk⟩ he).2 k hk j hj))⟩
    have hX:X⊆ A0 ∪ B:=by intro j hj; by_cases h:j∈A0; exact mem_union_left _ h; exact mem_union_right _ (mem_sdiff.mpr ⟨hj,h⟩)
    refine quietV _ A0 B hX hG ?_ ?_ hs (fun h=> Finset.disjoint_left.mp hG ha (h hi))
    · intro i hi; rw [fieldH f A0 B hG (fun v hv=> hF (hv.trans hi)) (hi.trans hX)]; apply siloes Xp Q M P (hp:=lowMark f w a (Finset.Subset.trans inter_subset_left hi) he) (hf:= lowMark f w a (Finset.Subset.trans inter_subset_left hi) he)
      · refine Finset.disjoint_left.mpr fun j hi hj=>?_ ; obtain ⟨a,ha,h₀⟩:=mem_biUnion.mp hi; obtain ⟨b,hb,h₁⟩:=mem_biUnion.mp hj; have hk:= (mem_inter.mp ha).2; have hl:=(mem_inter.mp hb).2; exact Finset.disjoint_left.mp (h a (hA hk) b (sdiff_subset hl) (fun h=> Finset.disjoint_left.mp hG hk (h.symm ▸ hl)) (hw a hk b hl)).1 h₀ h₁
      · intro i hi j hj; obtain ⟨a,ha,h₀⟩:=mem_biUnion.mp hi; obtain ⟨b,hb,h₁⟩:=mem_biUnion.mp hj; have hk:= (mem_inter.mp ha).2; have hl:=(mem_inter.mp hb).2; exact (h a (hA hk) b (sdiff_subset hl) (fun h=> Finset.disjoint_left.mp hG hk (h.symm ▸ hl)) (hw a hk b hl)).2.1 i h₀ j h₁
      intro i hi j hj; obtain ⟨a,ha,h₀⟩:=mem_biUnion.mp hi; obtain ⟨b,hb,h₁⟩:=mem_biUnion.mp hj; have hk:= (mem_inter.mp ha).2; have hl:=(mem_inter.mp hb).2; exact (h a (hA hk) b (sdiff_subset hl) (fun h=> Finset.disjoint_left.mp hG hk (h.symm ▸ hl)) (hw a hk b hl)).2.2 i h₀ j h₁
    change dawn (parties f ∅)=_; rw [hollow,alights]
lemma growth (v D:ℝ)(hv:1 ≤ v)(hf:∀ i⊆X,i.Nonempty → cents (f i) ≤ v^i.card)(hx:X.card ≤ l)(hD:1 ≤ D)(hh:∀ (x:Papers G (Patio A)),x∈Ledger (X.biUnion a) (X.biUnion w) (l*n) (l*m)→cents (dawn x) ≤ D*cents x): cents (Qy X) ≤ (v*(D*age l*moneyN l))^X.card:=by
   let f' i:= dawn (parties f i); let W:=D*age l
   have hy:1 ≤ W:= one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num))
   have h' i (hi:i∈ X.powerset) (hz:i.Nonempty): cents (f' i) ≤ (v*W)^i.card:=by
        have hp:= mem_powerset.mp hi; have hh':= (card_le_card hp).trans hx
        have hg:= money_fast f (probate G) v (fun j hj=> hf _ ((mem_powerset.mp hj).trans hp)) hv hh' -- syntax
        refine ((hh _ (leaguer (lowMark f w a hp he) (biUnion_subset_biUnion_of_subset_left _ hp) (biUnion_subset_biUnion_of_subset_left _ hp) (by gcongr) (by gcongr))).trans (mul_le_mul_of_nonneg_left hg (zero_le_one.trans hD))).trans (?_)
        rw [← mul_assoc,mul_pow, mul_comm (v^i.card)]; apply mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hy (show 1 ≤ i.card from card_pos.mpr hz)) (pow_nonneg (zero_le_one.trans hv) _)
   rw [← mul_assoc]; exact shopper f' (probate E) (v*W) X h' (one_le_mul_of_one_le_of_one_le hv hy) hx
end Chamber
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Chamber.cutoff
#print axioms YM.MassiveQCD.Play.Chamber.growth
