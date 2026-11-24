import YM.MassiveQCD.Ribbon.Axis
/-! # Extension of Wick & density injection operators, track parity under splits -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Ribbon
open QCD QCD.Grass QCD.Cove QCD.Creek Function Finset
open scoped Topology ContDiff BigOperators Classical
variable {A B C D:Type} [Fintype A][Fintype B][Fintype C][Fintype D]
variable (B)
noncomputable def carry (p:Alg A→L[ℂ] Alg C) : Alg (A⊕B)→L[ℂ]Alg (C⊕B):= ∑ s,(stake C s).comp (p.comp (scrape A s))
lemma carriage (p:Alg A→L[ℂ] Alg C)(x): carry B p x=restore C (fun s=> p (scrape A s x)):=by unfold carry; rw [_root_.sum_apply]; rfl
lemma wing (p:Alg A→L[ℂ] Alg C)(s:Finset B)(x) : scrape C s (carry B p x)= p (scrape A s x):=by rw [carriage,wide]
lemma speaks (p:Alg A→L[ℂ] Alg C)(s:Finset B)(x:Alg A): carry B p (stake A s x)=stake C s (p x):=vista C _ _ fun i=>by rw [wing,stakesX,stakesX]; split <;> first|rfl|exact map_zero _
lemma composes (p:Alg A→L[ℂ] Alg C)(q:Alg C→L[ℂ] Alg D)(x):carry B q (carry B p x)=carry B (q.comp p) x:=vista D _ _ fun i=>by rw [wing,wing,wing]; rfl
lemma trivialC (x:Alg (A⊕B)):carry B (ContinuousLinearMap.id ℂ (Alg A)) x=x:=vista A _ _ fun i=>by rw [wing]; rfl
variable {B}
noncomputable def shade (s:Finset B) : Bool:= decide (Odd s.card)
lemma healthy (s:Finset B): Hom (shade s) (mono s):=by
    by_cases hp:Odd s.card
    · rw [shade,decide_eq_true hp]; exact (grade_mono s).trans (by rw [hp.neg_one_pow,neg_one_smul])
    rw [shade,decide_eq_false hp]; have he: Even s.card:= (Nat.not_odd_iff_even).1 hp; exact (grade_mono s).trans (by rw [he.neg_one_pow,one_smul])
lemma even_stake (s:Finset B) (x:Alg A) (h:Hom (shade s) x): Plus (stake A s x):=by
   have he : Hom (shade s) (fiber B x):=by
      cases hp:shade s <;> rw [hp] at h; exact (embed_grade ..).trans (congr_arg _ h); exact (embed_grade ..).trans ((congr_arg (fiber B) (show grade x = -x from h)).trans (map_neg _ _))
   have hf: Hom (shade s) (quill A (mono s)):=by
      have hg:= healthy s; cases hp:shade s <;> rw [hp] at hg; exact (embed_grade ..).trans (congr_arg _ hg); exact (embed_grade ..).trans ((congr_arg (quill A) (show grade _ = -_ from hg)).trans (map_neg _ _))
   have hF:=he.mul hf; rw [Bool.xor_self] at hF; exact hF
def degreeSign (t:Finset B) : ℂ:= (-1:ℂ)^t.card
def biasG (t:Finset B) : Alg A→ₗ[ℂ]Alg A:= (degreeSign t) • grade.toLinearMap
lemma tense (t:Finset B)(x:Alg A) : grade (stake A t x)=stake A t (biasG t x):=by
    rw [markedOut,markedOut,map_mul,embed_grade,embed_grade,grade_mono t,map_smul]
    exact (mul_smul_comm ..).trans (by unfold biasG degreeSign; simp only [LinearMap.smul_apply,map_smul,smul_mul_assoc]; rfl) -- order
lemma tame (t:Finset B)(x:Alg (A⊕B)): scrape A t (grade x)= biasG t (scrape A t x):=by
    conv_lhs=>rw [← rewriteR A x,map_sum,map_sum];
    simp_rw [tense]; rw [sum_eq_single t]
    · rw [quid]
    · exact fun i _ hi=>by rw [stakesX,if_neg hi.symm]
    simp
lemma serene (t:Finset B){x:Alg (A⊕B)}(h:Plus x) : Hom (shade t) (scrape A t x):=by
    have hk:(degreeSign t) • grade (scrape A t x) = scrape A t x:=(tame t x).symm.trans (congr_arg _ h)
    by_cases he:Odd t.card
    · rw [shade,decide_eq_true he]; unfold degreeSign at hk; rw [he.neg_one_pow,neg_one_smul] at hk; exact neg_eq_iff_eq_neg.mp hk
    rw [shade,decide_eq_false he]; have hr:Even t.card:= Nat.not_odd_iff_even.1 he; unfold degreeSign at hk; rw [hr.neg_one_pow,one_smul] at hk; exact hk
lemma oriented (B:Type)[Fintype B] (p:Alg A→L[ℂ] Alg C)(h: ∀ x:Alg A,p (grade x)=grade (p x))(x) : carry B p (grade x)=grade (carry B p x):=vista C _ _ fun i=>by rw [wing,tame,tame,wing,biasG,biasG,LinearMap.smul_apply,LinearMap.smul_apply,map_smul]; exact congr_arg _ (h _)
lemma evenCarry (B:Type)[Fintype B](p: Alg A→L[ℂ] Alg C)(h:∀ x:Alg A,p (grade x)=grade (p x))(x)(ht:Plus x): Plus (carry B p x):=(oriented B p h x).symm.trans (congr_arg _ ht)
lemma wheel (s t:Finset B)(x y: Alg A): stake A s x* stake A t y= fiber B (x*(if shade s then grade y else y))* quill A (mono s*mono t):=by
    have ht: quill A (mono s)*fiber B y = fiber B (if shade s then grade y else y)* quill A (mono s):=by
       have h:=healthy s
       split
       next hs=>
        rw [hs] at h; let a:=quill A (mono s)
        have hk:Minus a:= by rw [Minus,show grade a=_ from embed_grade .., show grade (mono s)=-mono s from h,map_neg]
        exact (embed_grade (B:=A⊕B) Sum.inl y) ▸ ((Minus.slides hk (grade (fiber B y))).trans (by rw [grade_twice])).symm -- syntax
       next hs=>
        rw [Bool.eq_false_iff.mpr hs] at h; refine (Plus.central (x:=quill A (mono s)) ?_ (fiber B y)).symm.eq -- edit
        exact (embed_grade ..).trans (congr_arg _ h)
    rw [markedOut,markedOut,map_mul,map_mul,mul_assoc, ← mul_assoc (quill A (mono s)),ht]; simp only [mul_assoc]
lemma carries_r (p:Alg A→L[ℂ] Alg C) (x:Alg (A⊕B))(y:Alg B): carry B p (x * quill A y)= carry B p x * quill C y:=by
   have hg (a:Alg A)(y:Alg B): carry B p (fiber B a*quill A y)=fiber B (p a)*quill C y:=by rw [← write y,map_sum,map_sum,Finset.mul_sum,map_sum, Finset.mul_sum]; exact sum_congr rfl fun i _=> by rw [map_smul,map_smul,mul_smul_comm,mul_smul_comm,map_smul]; exact congr_arg _ (speaks B p ..)
   rw [← rewriteR A x,Finset.sum_mul,map_sum,map_sum,Finset.sum_mul]; refine sum_congr rfl fun i _=>?_; rw [speaks,markedOut,markedOut,mul_assoc,mul_assoc,← map_mul,← map_mul,hg]
lemma ledger_alg (p:Alg A→ₐ[ℂ]Alg C)(h:∀ x,p (grade x)=grade (p x))(x y:Alg (A⊕B)): let q:=carry B p.toLinearMap.toContinuousLinearMap; q (x*y)=q x*q y:=by
   intro q; let t:= p.toLinearMap.toContinuousLinearMap
   rw [← rewriteR A x,← rewriteR A y]; simp only [Finset.mul_sum,sum_mul,map_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
   -- read twice
   rw [wheel,show q _=_ from speaks B t j _,show q _=_ from speaks B t i _,wheel]
   unfold q; rw [carries_r,← quiet,speaks,quiet]; congr 2; change p _ = t _ * _; rw [map_mul]; split<;> first|rfl|exact congr_arg _ (h _)
end YM.MassiveQCD.Ribbon
