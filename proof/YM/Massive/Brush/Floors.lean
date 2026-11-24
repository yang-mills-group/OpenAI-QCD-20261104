import YM.Massive.PCAC.Smalt
import YM.QCD.Stew.Pump
/-! Tail calculus for the bias estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
namespace Loft
open Stew
variable [DecidableEq A] {x y : Alg A}{m n:ℕ}
-- linear subspace in every finite algebra
noncomputable def floor (A:Type*) [Fintype A] (m:ℕ) : Submodule ℂ (Alg A):= ⨅ s: Finset A, ⨅ (_: s.card< m), LinearMap.ker (coef s)
omit [DecidableEq A]
lemma test {x:Alg A} : x∈floor A m ↔ ∀ s:Finset A,s.card< m→ coef s x=0:=by simp [floor]
lemma wage (h:x∈ layer A n)(hh:m≤n): x∈floor A m:=test.mpr fun s he=> spectrum h s (ne_of_lt (he.trans_le hh))
lemma there (x:Alg A): x∈ floor A 0:=test.mpr fun _ h=> False.elim (Nat.not_lt_zero _ h)
lemma reduce (hp:x∈floor A n)(hu:m≤n):x∈floor A m:=test.mpr fun s hs=> (test.mp hp) s (hs.trans_le hu)
lemma pays (h:x∈floor A m)(ht:y∈floor A n): x*y∈ floor A (m+n):=by
   rw [← write x, ← write y]; simp_rw [sum_mul,mul_sum]; apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _
   by_cases h1:i.card< m; · rw [test.mp h i h1,zero_smul,zero_mul]; exact Submodule.zero_mem _
   by_cases h2:j.card<n; · rw [test.mp ht j h2,zero_smul,mul_zero]; exact Submodule.zero_mem _
   rw [smul_mul_assoc,mul_smul_comm]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (wage (layer_mul (homogeneous _) (homogeneous _)) (by omega)))
lemma expiring (h:x∈floor A m)(n:ℕ): x^n∈floor A (n*m):=by
    induction n with | zero=> simpa using! there (1:Alg A) | succ i ih=> rw [pow_succ,add_mul,one_mul]; exact pays ih h
lemma holds {z:ℕ→ Alg A}(h:HasSum z x)(p:∀ i,z i∈ floor A m): x∈floor A m:=by refine Submodule.closed_of_finiteDimensional (floor A m)|>.mem_of_tendsto h (Filter.Eventually.of_forall fun q:Finset ℕ=> Submodule.sum_mem _ fun i _=> p i)
lemma exhaust (h:x∈floor A m): exp x-1-x∈floor A (m+m):=by
   let g(n:ℕ):=(n.factorial:ℂ)⁻¹ • x^n; have hh: HasSum g (exp x) := exp_series_hasSum_exp' x; rw [←hasSum_nat_add_iff' (k:=2)] at hh
   have hu(n:ℕ): g (n+2)∈ floor A (m+m):=Submodule.smul_mem _ _ (reduce (expiring h (n+2)) (by rw [add_mul]; omega)); have hs:=holds hh hu
   rw [sum_range_succ,sum_range_one,show g 0=1 by simp [g],show g 1=x by simp [g],←sub_sub] at hs; exact hs
lemma exhausted (h:x∈floor A m): exp x-1∈ floor A m :=by
   have ht := Submodule.add_mem (floor A m) (reduce (exhaust h) (by omega : m≤ m+m)) h; rwa [sub_add_cancel] at ht
lemma lowered (h:x∈floor A m)(i:A): vary i x∈ floor A (m-1):=by
    rw [←write x, map_sum]; apply Submodule.sum_mem; intro s _; by_cases he:s.card< m; · rw [test.mp h s he,zero_smul,map_zero]; exact Submodule.zero_mem _
    rw [map_smul]; exact Submodule.smul_mem _ _ (wage (lowers ..) (by omega))
lemma constant_one : coef ∅ (1: Alg A)=1:=by rw [←mono_empty]; exact read ∅
lemma body_exp (h:x∈floor A 1): coef ∅ (exp x)=1:=by have hh:= test.mp (exhausted h) ∅ (by simp); rwa [map_sub, sub_eq_zero,constant_one] at hh
lemma change_pair(k i:A)(x:Dirac A)(h:x∈floor (Pairs A) m) : pairD k i x∈floor (Pairs A) (m-2):=by
    rw [show m-2=m-1-1 from by omega]; exact lowered (lowered h _) _
lemma unmarked (x:Dirac A)(h:x∈floor (Pairs A) m)(V:Sour A) : lap V x∈floor (Pairs A) (m-2):=by unfold lap; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply]; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (change_pair _ _ x h)
lemma unquote (x y: Dirac A)(h:x-y∈floor (Pairs A) 3) : traceP x=traceP y:=by
    ext i j; have hv:= test.mp (change_pair j i _ h) ∅ (by simp); rw [map_sub,map_sub,sub_eq_zero] at hv; exact congr_arg ( -·) hv
-- compare pure exponential quartet.
lemma multiply_price (x y:Alg A)(hh:x∈floor A 2)(hp:y∈floor A 4)(hb:Commute x y) : exp (x+y)-(exp x+y)∈floor A 6:=by
   have h₁:= exhausted hh; have h₂:= exhaust hp
   have he:= pays h₁ hp; have ht:= pays (there (exp x)) h₂
   rw [algebra_exp_add hb]; rw [show exp x*exp y-(exp x+y)= (exp x-1)*y + exp x*(exp y-1-y) from (by rw [mul_sub,mul_sub,mul_one,sub_mul,one_mul]; abel)]; norm_num at he ht; exact (floor A 6).add_mem he (reduce ht (by decide))
lemma quarter_hi (D:Sour A)(x:Dirac A)(h:x-form D∈ floor (Pairs A) 4) : exp x-(gauss D+(x-form D)) ∈ floor (Pairs A) 6:=by
   let f:=form D; let z:=x-f; have he:= multiply_price f z (wage (form_two D) le_rfl) h ((form_plus D).central z).symm; rw [show f+z=x from add_sub_cancel ..] at he; exact he
lemma trace_add (x y:Dirac A): traceP (x+y)=traceP x+traceP y:=by ext i j; simp [traceP,add_comm]
set_option maxHeartbeats 500000 in
lemma quarter (D:Sour A)(x:Dirac A)(h:x-form D ∈ floor (Pairs A) 4)(V:Sour A) : traceP (lap V (exp x))= traceP (lap V (gauss D))+traceP (lap V (x-form D)):=by
   have hu:=quarter_hi D x h; let z:=x-form D; let E:=gauss D
   have hL: traceP (lap V (exp x))=traceP (lap V (E+z)):=unquote _ _ (by rw [←map_sub]; exact reduce (unmarked _ hu V) (by decide))
   rw [hL,map_add, trace_add]
end Loft
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.Loft.quarter
