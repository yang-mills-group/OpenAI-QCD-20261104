import YM.Play.Cider
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix
namespace Oce
variable {S T:Type*}[CommRing T]{r:ℕ}
def rise (f:S→T)(s:Finset S)(n:ℕ) :=∑ i∈s.powerset,(-1:T)^(s.card-i.card)*(∑ j∈i,f j)^n
lemma leap (f:S→T)(s:Finset S)(j:S)(h:j∉s)(n:ℕ): rise f (insert j s) n= ∑ i∈range n,(Nat.choose n i:T)*f j^(n-i)*rise f s i:=by
    let g (v: Finset S):= (-1:T)^((insert j s).card-v.card)*(∑ k∈v,f k)^n; change (∑ i ∈(insert j s).powerset,g i)=_; rw [Cove.sprinkle s j h,← sum_add_distrib]; unfold rise; simp_rw [mul_sum]; rw [sum_comm (s:=range n)]; -- check arg.
    apply sum_congr rfl; intro i hi; unfold g; have h':j∉i:=fun he=> h ((mem_powerset.mp hi) he); rw [card_insert_of_notMem h,card_insert_of_notMem h',sum_insert h']; let x:=∑ k ∈ i,f k; rw [show s.card+1-i.card=s.card-i.card+1 by have h:=card_le_card (mem_powerset.mp hi); omega, pow_succ',← smul_eq_mul,← smul_eq_mul] -- avoid
    rw [add_comm (f j), add_pow, Finset.sum_range_succ]; push_cast
    ring_nf; simp [Finset.sum_mul]
lemma going (f:S→T)(s:Finset S)(n:ℕ)(he:n≤s.card) : rise f s n=if n=s.card then n.factorial*∏ i∈s,f i else 0:=by
    induction s using Finset.induction_on generalizing n with
    | empty=> have h:n=0:=by simpa using he
              subst n; simp [rise]
    | insert i s hi ih=>
     rw [leap f s i hi,Finset.prod_insert hi, card_insert_of_notMem hi]; rw [card_insert_of_notMem hi] at he; split
     next h=>
        subst n; rw [sum_eq_single s.card, ih _ le_rfl,if_pos rfl, Nat.choose_succ_self_right, Nat.factorial_succ, Nat.add_sub_cancel_left,pow_one]; push_cast; ring -- help
        intro i hi h'; have h:i≤ s.card:=Nat.le_of_lt_succ (mem_range.mp hi); rw [ih i h,if_neg h',mul_zero]; simp
     next h=> apply sum_eq_zero; intro i hi; have h₀:=mem_range.mp hi; have hv:i<s.card:=(by omega); rw [ih _ hv.le,if_neg (ne_of_lt hv),mul_zero]
end Oce
end YM.QCD.Bera
#print axioms YM.QCD.Bera.Oce.going
