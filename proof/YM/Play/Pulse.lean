import YM.Play.Pit
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace Cupola Ribbon QCD.Bera QCD.Anomaly
open MeasureTheory BigOperators Matrix
open scoped Topology BigOperators ContDiff Classical
variable {I K A B G E: Type}
namespace Chamber
local notation "H"=> Finset I
variable {X Y: Finset I}{L:Finset (Finset I)}{n m:ℕ}{s t v:ℝ}
section commerce
variable [CommRing K]
structure Sal (g:K→ℝ): Prop where
  non : ∀ x,0 ≤ g x
  tri : ∀ x y,g (x+y) ≤ g x+g y
  mul : ∀ x y,g (x*y) ≤ g x*g y
  zero : g 0=0
  neg : ∀ x,g (-x)=g x
  one : g 1=1
namespace Sal
variable {g:K→ℝ}(h:Sal g)
include h
lemma shill (a b:K): g (a-b)≤ g a+g b:=by rw [sub_eq_add_neg]; exact (h.tri _ _).trans_eq (by rw [h.neg])
lemma suma (s:Finset B)(f:B→K): g (∑ i∈s,f i)≤ ∑ i∈s,g (f i):=by induction s using Finset.induction_on with
 | empty=> simp [h.zero]
 | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (h.tri ..).trans (add_le_add_right ih _)
lemma prodB (s:Finset B)(f:B→K): g (∏ i∈s,f i)≤ ∏ i∈s,g (f i):=by induction s using Finset.induction_on with
 | empty=> simp [h.one]
 | insert i s hi ih=> rw [prod_insert hi,prod_insert hi]; exact (h.mul ..).trans (mul_le_mul_of_nonneg_left ih (h.non _))
end Sal
variable (f w:Finset I→ K) -- notation variable ⚠
-- budget

def age (n:ℕ):ℝ:= 2^(2^n:ℕ)
lemma passport (i:H)(h:i.card ≤ m): ((registry i).card:ℝ) ≤ age m:=by
    have ht := card_le_card (filter_subset (fun x:Finset H=> ∅∉x∧ x.biUnion id=i∧(x:Set H).PairwiseDisjoint id) i.powerset.powerset); rw [Finset.card_powerset,Finset.card_powerset] at ht
    unfold age; apply le_trans (b:=↑(2^(2^i.card:ℕ):ℕ)); exact_mod_cast (show (registry i).card ≤ _ from ht)
    push_cast; gcongr <;> norm_num
variable {g:K→ℝ}(h:Sal g)
include h
lemma money_fast (v:ℝ) (hp:∀ i∈ X.powerset,i.Nonempty → g (f i) ≤ v^i.card)(hv:1≤v) (he:X.card ≤ m): g (parties f X) ≤ (age m)*v^X.card:=by
   let A:=registry X; apply le_trans (h.suma _ _); have hh : 0 ≤ v:=zero_le_one.trans hv
   refine (sum_le_sum (g:=fun _=>v^X.card) (fun i hi=> (h.prodB ..).trans ((prod_le_prod (fun k _=>h.non (f k)) (fun k hk=> hp k (mem_powerset.mpr (member hi hk).2) (member hi hk).1)).trans (?_)))).trans (?_); rw [prod_pow_eq_pow_sum, patrons hi]
   rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (passport X he) (pow_nonneg hh _)
noncomputable def moneyN : ℕ→ ℝ
 | 0=>1
 | n+1=>moneyN n * (1+age (n+1))
omit h
private lemma rich (m:ℕ):1 ≤ moneyN m:=by induction m with
  | zero=> exact le_rfl
  | succ i ih=> exact one_le_mul_of_one_le_of_one_le ih (le_add_of_nonneg_right (by unfold age; positivity))
private lemma ups : Monotone moneyN:=monotone_nat_of_le_succ (fun n=>le_mul_of_one_le_right (zero_le_one.trans (rich n)) (le_add_of_nonneg_right (by unfold age; positivity)))
include h
lemma shopper (v:ℝ)(X:H)(hp:∀ i∈ X.powerset,i.Nonempty → g (f i) ≤ v^i.card)(hv:1≤v)(hX:X.card  ≤ m): g (cetacea f X) ≤ (v*moneyN m)^X.card:=by
    suffices he: ∀ n:ℕ,∀ i :H,∀ v:ℝ,1 ≤v→ i.card=n→(∀ j∈i.powerset,j.Nonempty → g (f j) ≤ v^j.card)→ g (cetacea f i) ≤ (v*moneyN n)^n by
       have hν:1 ≤ v * moneyN X.card:=one_le_mul_of_one_le_of_one_le hv (rich _); exact (he X.card X v hv rfl hp).trans (pow_le_pow_left₀ (zero_le_one.trans hν) (mul_le_mul_of_nonneg_left (ups hX) (zero_le_one.trans hv)) _)
    intro n; induction n using Nat.strong_induction_on with
    | h n ih=>
       intro i v hv hz hI; cases n with
       | zero=> have hi:=card_eq_zero.mp hz; rw [cet,if_neg (by simp [hi]),h.zero,pow_zero]; exact zero_le_one
       | succ k=>
         have hC: i.Nonempty:= card_pos.mp (by omega); have hp':g (f i)≤ v^(k+1):= hz ▸ hI i (mem_powerset_self i) hC; let K₀:= v*moneyN k; have hk:1 ≤ K₀:=one_le_mul_of_one_le_of_one_le hv (rich k)
         have hP (p) (hp:p∈cut i): g (∏ j∈p,cetacea f j) ≤ K₀^(k+1):=by
             have hA j (hj:j∈p): g (cetacea f j) ≤ K₀^j.card:=by
                have hl:=limit hp hj; have he:j.card≤k:=Nat.le_of_lt_succ ((card_lt_card hl).trans_le hz.le); refine (ih _ (Nat.lt_succ_of_le he) j v hv rfl (fun l hh=> hI l (mem_powerset.mpr ((mem_powerset.mp hh).trans (member (mem_of_mem_erase hp) hj).2)))).trans (pow_le_pow_left₀ (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hv (rich _))) (mul_le_mul_of_nonneg_left (ups he) (zero_le_one.trans hv)) _)
             refine (h.prodB p _).trans ((prod_le_prod (fun i _=>h.non (cetacea f i)) hA).trans ?_); rw [prod_pow_eq_pow_sum, patrons (mem_of_mem_erase hp),hz]
         have hh:g (∑ j ∈ cut i,∏ x∈j,cetacea f x) ≤ age (k+1)*K₀^(k+1):=by
             refine (h.suma _ _).trans ((sum_le_sum hP).trans ?_); rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr (card_le_card (erase_subset ..))).trans (passport i hz.le)) (pow_nonneg (zero_le_one.trans hk) _)
         rw [cet,if_pos hC]; refine (h.shill _ _).trans ((add_le_add (hp'.trans (pow_le_pow_left₀ (zero_le_one.trans hv) (le_mul_of_one_le_right (zero_le_one.trans hv) (rich k)) _)) hh).trans (?_))
         let P:=1+age (k+1); have hu:1 ≤P:=le_add_of_nonneg_right (by unfold age; positivity)
         change K₀^(k+1)+age _*K₀^(k+1) ≤ (v * moneyN (k+1))^(k+1); rw [show K₀^(k+1)+age (k+1)*K₀^(k+1)=P*K₀^(k+1) from (by unfold P; ring), show v*moneyN (k+1)=P*K₀ from (by rw [moneyN]; unfold P K₀; ring),mul_pow P K₀]
         exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hu (show 1 ≤ k+1 by omega)) (pow_nonneg (zero_le_one.trans hk) _)
end commerce
noncomputable def probate {Z:Type}[Fintype Z](G:Type) : Sal (cents (F:=Patio Z) (A:= G)):= ⟨fun i=> by exact cent _,wealth,bag,zero_cent,absorb,by rw [← map_one (f:=MvPolynomial.C),coinride,norm_one]⟩
lemma marksV (Z:Type)[NormedCommRing Z][NormOneClass Z]: Sal (norm:Z→ℝ):=⟨norm_nonneg,norm_add_le,norm_mul_le,norm_zero,norm_neg, norm_one⟩
end Chamber
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Chamber.shopper
