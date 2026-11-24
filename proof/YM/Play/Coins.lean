import YM.Play.Pulse
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace Cupola Ribbon QCD.Bera QCD.Anomaly
open MeasureTheory BigOperators Matrix
open scoped Topology BigOperators ContDiff Classical
variable {I K A B G E: Type}
namespace Chamber
local notation "H"=> Finset I
variable {X Y: Finset I}{L:Finset (Finset I)}{n m l:ℕ}{s t v:ℝ}
variable [CommRing K]
namespace Sal
variable {g:K→ℝ}(h:Sal g)
include h
lemma prodD (X: Finset I)(a b:I→K)(hp:∀ i∈X,g (a i) ≤ v)(he:∀ i∈X,g (b i) ≤ v)(ht:∀ i∈X,g (a i - b i) ≤ s)(hv:1 ≤ v)(hs:0 ≤ s): g ((∏ i∈X,a i)-∏ i∈X,b i) ≤ X.card*s*v^X.card:=by
    have hz:0 ≤ v:=zero_le_one.trans hv
    induction X using Finset.induction_on with
    | empty=> rw [prod_empty,prod_empty, sub_self,h.zero,card_empty]; simp
    | insert i X hi ih=>
      let U:=∏ i∈X,a i; let V:=∏ i∈X,b i; have hr:g U ≤ v ^ X.card:= (h.prodB X a).trans ((prod_le_prod (fun i _=> h.non _) (fun i hi=> hp i (mem_insert_of_mem hi))).trans_eq (prod_const ..)); have h_:0 ≤ g U:= h.non _
      have hi₁:g ((a i-b i)*U) ≤ s*v^X.card:=(h.mul ..).trans (mul_le_mul (ht i (mem_insert_self ..)) hr h_ hs)
      have hx: g (U - V) ≤ X.card*s*v^X.card:= ih (fun i hi=>hp i (mem_insert_of_mem hi)) (fun i hi=>he i (mem_insert_of_mem hi)) (fun i hi=>ht i (mem_insert_of_mem hi))
      rw [prod_insert hi, prod_insert hi]; change g (a i*U - b i * V) ≤ _
      rw [show a i*U-b i*V=(a i-b i)*U+b i*(U-V) by ring]; refine (h.tri _ _).trans ((add_le_add hi₁ ((h.mul ..).trans (mul_le_mul (he i (mem_insert_self ..)) hx (h.non _) hz))).trans ?_)
      rw [card_insert_of_notMem hi,pow_succ]; push_cast; have ht:= le_mul_of_one_le_right (mul_nonneg hs (pow_nonneg hz X.card)) hv; linarith only [ht]
lemma sumD (X: Finset I) (a b:I→K)(ht:∀ i∈X,g (a i-b i) ≤ s): g ((∑ i∈X,a i)-∑ i∈X,b i) ≤ X.card*s:=by
   rw [← Finset.sum_sub_distrib]; exact (h.suma _ _).trans ((sum_le_sum ht).trans_eq (by simp))
end Sal
variable {g:K→ℝ}(h:Sal g)(f w: Finset I→K)
def face (l:ℕ)(v:ℝ):ℝ:=age l* (2^l:ℕ)*v^(2^l:ℕ)
include h
lemma settlers (S: Finset (Finset (Finset I))) (hS:S⊆registry X) (hx:X.card ≤ l) (ht:∀ i∈S,∀ j∈i,g (f j - w j) ≤ s) (hf:∀ i∈S,∀ j∈i,g (f j) ≤ v) (hw:∀ i∈S,∀ j∈i,g (w j) ≤ v) (hv:1 ≤ v)(hs:0 ≤ s): g ((∑ i∈S,∏ j∈i,f j)-∑ i∈S, ∏ j∈i,w j) ≤ face l v * s:=by
   have he:0 ≤ v:=zero_le_one.trans hv
   have hh i (hi:i∈S) : g ((∏ j∈i,f j)-∏ j∈i,w j) ≤ (2^l:ℕ)*s*v^(2^l:ℕ):=by
       have hg:i.card ≤ 2^l:= by
          have h:=card_le_card (mem_powerset.mp (mem_filter.mp (hS hi)).1); rw [card_powerset] at h; exact h.trans (pow_le_pow_right₀ (by norm_num) hx)
       exact (h.prodD i _ _ (hf i hi) (hw i hi) (ht i hi) hv hs).trans (by gcongr)
   refine (h.sumD _ _ _ hh).trans ((mul_le_mul_of_nonneg_right (le_trans (Nat.cast_le.mpr (card_le_card hS)) (passport _ hx)) (show (0:ℝ) ≤ (2^l:ℕ)*s*v^(2^l:ℕ) by positivity)).trans_eq (by unfold face; push_cast; ring))
lemma spendingX (X: Finset I)(hx:X.card ≤ l)(hf:∀ i⊆X,i.Nonempty→ g (f i) ≤ v)(hw:∀ i⊆X,i.Nonempty→ g (w i) ≤ v)(ht:∀ i⊆X,i.Nonempty → g (f i-w i) ≤ s)(hv:1 ≤ v)(hs:0 ≤ s): g (parties f X - parties w X) ≤ face l v * s:=settlers h _ _ _ (Subset.refl _) hx (fun i hi j hj=>ht _ (member hi hj).2 (member hi hj).1) (fun i hi j hj=>hf _ (member hi hj).2 (member hi hj).1) (fun i hi j hj=>hw _ (member hi hj).2 (member hi hj).1) hv hs
lemma spentX (X:Finset I)(hx:X.card ≤ l)(hv:1 ≤ v)(hs:0 ≤ s)(hf:∀ i⊆X,i.Nonempty→ g (cetacea f i) ≤ v)(hw:∀ i⊆X,i.Nonempty→ g (cetacea w i) ≤ v)(ht:∀ i⊆X,i.Nonempty → g (f i-w i) ≤ s): g (cetacea f X - cetacea w X) ≤ (face l v+1)^l * s:=by
    have hv:0 ≤ v:=zero_le_one.trans hv; have he:0 ≤ face l v:=by unfold face age; positivity
    suffices he':∀ n:ℕ,∀ i⊆X,i.card=n → g (cetacea f i -cetacea w i) ≤ (face l v+1)^n*s from (he' _ X (Subset.refl X) rfl).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_add_of_nonneg_left he) hx) hs)
    intro n; induction n using Nat.strong_induction_on with
    | h n ih=>
      intro i hi ht'; rcases i.eq_empty_or_nonempty with ha|ha; · rw [cet f i,cet w i,if_neg (by simp [ha]),if_neg (by simp [ha]),sub_self,h.zero]; have hp:0 ≤ face l v+1:=add_nonneg he zero_le_one; positivity
      have hn:0 < n:= ht' ▸ Finset.card_pos.mpr ha
      let a:= ∑ j∈cut i,∏ y∈j,cetacea f y; let b:=∑ j∈cut i, ∏ y∈j,cetacea w y; cases n with
      | zero=>omega
      | succ n=>
           let d:=face l v; have hd:1 ≤ d+1:= le_add_of_nonneg_left he; let t':=(d+1)^n*s
           have h0 : s ≤ t' := le_mul_of_one_le_left hs (one_le_pow₀ hd)
           have hh : g (a-b) ≤ d * ((d+1)^n *s):=by
                  refine settlers h _ _ _ (Finset.erase_subset ..) ((card_le_card hi).trans hx) (fun j hj k hk=>?_) (fun j hj k hk=>hf _ ((member (mem_of_mem_erase hj) hk).2.trans hi) (member (mem_of_mem_erase hj) hk).1) (fun j hj k hk=>hw _ ((member (mem_of_mem_erase hj) hk).2.trans hi) (member (mem_of_mem_erase hj) hk).1) (‹1 ≤ v›) (hs.trans h0); have hv:= (card_lt_card (limit hj hk)).trans_le ht'.le; exact (ih _ hv k ((member (mem_of_mem_erase hj) hk).2.trans hi) rfl).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd (Nat.le_of_lt_succ hv)) hs)
           rw [cet f i,cet w i,if_pos ha,if_pos ha]; change g (f i-a-(w i-b)) ≤ _; rw [show f i-a-(w i-b)= (f i-w i) -(a-b) from by abel,pow_succ']
           refine (h.shill _ _).trans ((add_le_add ((ht _ hi ha).trans h0) hh).trans_eq (by unfold t' d; ring)) -- unfold
end Chamber
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Chamber.spentX
