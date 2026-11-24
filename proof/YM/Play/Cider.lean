import YM.Next.RANK.Rise
import YM.Play.Dukes
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Finsupp Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T: Type*}
section Goods
variable {F:Type*}[NormedCommRing F][NormedAlgebra ℂ F]{X U V:Finset A}{Z :Finset B}{n m i k:ℕ}{c d k₀ s t:ℝ}
-- norm L1
abbrev Papers (A F:Type*)[CommSemiring F]:=MvPolynomial A F
local notation "P"=> Papers A F
def cents (p:Papers A F):= ∑ i∈p.support,‖coeff i p‖
def len (s:A →₀ ℕ) :ℕ:=weight (fun _=>1) s
lemma cent (x:P):0 ≤ cents x := Finset.sum_nonneg (fun i _=> norm_nonneg _)
lemma solely (s:A→₀ℕ)(x:F): cents (monomial s x)=‖x‖:=by unfold cents; rw [← MvPolynomial.sum_def (b:=fun i (x:F)=>‖x‖)]; exact MvPolynomial.sum_monomial_eq (by simp)
@[simp] lemma zero_cent : cents (0:P)=0:=by simp [cents]
@[simp] lemma absorb (x:P): cents (-x)=cents x:=by simp [cents]
lemma coinride (c:F): cents (MvPolynomial.C (σ:=A) c)=‖c‖:= solely ..
lemma wealth (p q:P): cents (p+q) ≤cents p+cents q:=by
   let W:=p.support∪q.support; have he (x:P)(h:x.support⊆W): cents x=∑ i∈W,‖coeff i x‖:=sum_subset h fun i _ hp=> by simp only [MvPolynomial.notMem_support_iff.mp hp, norm_zero]
   rw [he (p+q) MvPolynomial.support_add,he p subset_union_left,he q subset_union_right,← Finset.sum_add_distrib]; exact sum_le_sum fun i _=> by rw [coeff_add]; exact norm_add_le ..
lemma money (p:Finset B)(f:B→P): cents (∑ i∈p,f i)≤∑ i∈p,cents (f i):=by
    induction p using Finset.induction_on with
    | empty => simp
    | insert i p hi ih=> rw [sum_insert hi,sum_insert hi]; exact (wealth (f i) _).trans (add_le_add_right ih _)
lemma bag (p q:P): cents (p*q) ≤ cents p*cents q:=by
    rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]; apply (money _ _).trans
    unfold cents; rw [Finset.sum_mul_sum]; apply Finset.sum_le_sum; intro i _; exact (money _ _).trans (Finset.sum_le_sum fun j _=> (solely ..).trans_le (norm_mul_le ..))
lemma smul_cent (p:P)(a:ℂ): cents (a • p) = ‖a‖*cents p:=by
    by_cases he:a=0
    · simp [he]
    have hv:(a • p).support=p.support:= by ext i; simp [he,coeff_smul]
    unfold cents; rw [hv,Finset.mul_sum]; exact sum_congr rfl fun i _=> (by rw [coeff_smul,norm_smul])
structure tags (U:Finset A) (n:ℕ) (s:A→₀ℕ) : Prop where
    points : s.support⊆U
    size : len s ≤ n
-- guard each coefficient later; scalar support here.
def Camp (U:Finset A)(n:ℕ): Submodule ℂ (Papers A F) where
   carrier:= {x|∀ i∈x.support,tags U n i}
   zero_mem' :=by simp
   add_mem' :=by intro x y h g i hi; exact (mem_union.mp (MvPolynomial.support_add hi)).elim (h i) (g i)
   smul_mem' :=by
      intro a x h i hi; refine h i (MvPolynomial.mem_support_iff.mpr (?_)); exact fun hx=> MvPolynomial.mem_support_iff.mp hi (by rw [coeff_smul,hx,smul_zero])
lemma stampC {x:P}(h:x∈Camp U n)(i)(hi:i∈ x.support): tags U n i := h i hi
lemma shadeC {x:P}(h:x∈Camp U n)(hU:U⊆V)(hn:n≤m): x∈ Camp V m:=fun i hi=> ⟨(stampC h i hi).points.trans hU,(stampC h i hi).size.trans hn⟩
lemma sparks {s:A→₀ℕ}(b:F)(h:tags U n s): monomial s b∈Camp U n:=by
   intro i hi; have hv: i=s:= by
        by_contra h; apply MvPolynomial.mem_support_iff.mp hi; simp [h,Ne.symm h]
   exact hv.symm ▸ h
lemma token (x:F): MvPolynomial.C x∈Camp U n:= by
   have hp: tags U n (0:A→₀ℕ) :=⟨by simp,by simp [len]⟩
   exact sparks x hp
lemma genesis : (1:P) ∈ Camp U n :=by rw [← map_one (MvPolynomial.C:F →+* P)]; exact token _ -- R' spelling
lemma adding (a b:A→₀ℕ)(h:tags U n a)(g:tags U m b):tags U (n+m) (a+b):=⟨(Finsupp.support_add ..).trans (Finset.union_subset h.points g.points), (map_add (weight (fun _=>1)) ..).trans_le (add_le_add h.size g.size)⟩
lemma manufacture {x y:P}(h:x∈ Camp U n)(he:y∈Camp U m): x*y ∈ Camp U (n+m):=by
   rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]; exact Submodule.sum_mem _ fun i hi=> Submodule.sum_mem _ fun j hj=>sparks _ (adding i j (stampC h i hi) (stampC he j hj))
lemma xrise (i:A)(hi:i∈U): (MvPolynomial.X i:P) ∈ Camp U 1:=by
   refine sparks (1:F) ⟨(?_),by unfold len; rw [Finsupp.weight_single]; simp⟩; exact (Finsupp.support_single_subset).trans (singleton_subset_iff.mpr hi)
-- coordinates.List economical
noncomputable def winks (L:List A) : P:= (L.map (MvPolynomial.X (R:=F))).prod
private lemma sprout_impl (x:A→₀ ℕ)(h:x.support⊆U): ∃ L:List A,(∀ i∈L,i∈U) ∧ L.length=len x ∧(∀ p:F, C p*winks L=monomial x p):=by
    suffices hh: ∀ n:ℕ, ∀ x:A→₀ℕ, x.support⊆U→len x=n→ ∃ L:List A,(∀ i∈L,i∈U) ∧ L.length=len x∧ (∀ p:F,C p*winks L=monomial x p) from hh _ _ h rfl
    intro n; induction n with
    | zero=> intro x hx he; have hp:x=0:=by
                unfold len at he; -- weight one sum. positivity
                by_contra hn; have hm:x.support.Nonempty:= Finsupp.support_nonempty_iff.mpr hn; obtain ⟨i,hi⟩:=hm; have h':0<x i:= Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi); simp only [weight_apply, nsmul_eq_mul, mul_one, Finsupp.sum] at he; exact (sum_pos' (fun _ _=>Nat.zero_le _) ⟨_,hi,h'⟩).ne' he
             subst x; exact ⟨[],by simp,by simp [len],fun p=>by simp [winks]⟩
    | succ n ih=>
      intro x hx he; have hz:x ≠0:=by intro h; simp [h,len] at he
      obtain ⟨i,hi⟩:=Finsupp.support_nonempty_iff.mpr hz; let A':= Finsupp.single i (1:ℕ); have ha:A' ≤ x:=by
           intro j; by_cases h:j=i; subst j; unfold A'; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi); unfold A'; rw [Finsupp.single_eq_of_ne h]; exact Nat.zero_le _
      let p:= x-A'; have hp :p +A'=x:= tsub_add_cancel_of_le ha; have hs:p.support⊆ x.support:=fun j h=> by
           rw [←hp,Finsupp.mem_support_iff, Finsupp.add_apply]; have h:=Finsupp.mem_support_iff.mp h; omega
      have hh:len p+1=len x:=by rw [← hp]; unfold len A'; rw [map_add,weight_single]; simp
      obtain ⟨L,hH,hV,hY⟩:= ih p (hs.trans hx) (by omega); refine ⟨i::L,by simp only [List.mem_cons]; rintro j (rfl|hh); exact hx hi; exact hH j hh,by rw [List.length_cons,hV,hh],?_⟩
      intro b; rw [show winks (F:=F) (i::L) = winks L*MvPolynomial.X i from (by unfold winks; rw [List.map_cons,List.prod_cons,mul_comm]), ← mul_assoc,hY b, MvPolynomial.X,monomial_mul]; rw [show _=x from hp,mul_one]
lemma sprout (x:A→₀ℕ)(b:F)(h:x.support⊆U):∃ L:List A,(∀ i∈L,i∈U)∧ L.length=len x∧ monomial x b=C b*winks L:=by obtain ⟨L,ha,he,h⟩:=sprout_impl (F:=F) _ h; exact ⟨L,ha,he,(h b).symm⟩
end Goods
end YM.QCD.Bera
#print axioms YM.QCD.Bera.manufacture
#print axioms YM.QCD.Bera.sprout
