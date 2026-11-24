import YM.QCD.Nola.Pam
import YM.QCD.Creek.Crest
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι κ A:Type*} {n : Side} {k:ℕ} [Fintype A]{s t a χ δ b:ℝ}
open Kites Pads
abbrev Peak (A: Type*)[Fintype A]:= {v:Finset A//Even v.card∧0<v.card}
noncomputable def interesting (F:Patio A) (s:Peak A):Patio A:= ⟨coef s.val F.val • mono s.val,by
     have he: grade (coef s.val F.val • mono s.val)=_ := (map_smul _ _ _).trans (congr_arg _ (Grass.grade_mono _)); change Plus _; unfold Plus; rw [map_smul, Grass.grade_mono,s.property.1.neg_one_pow]; simp⟩
noncomputable def edges (p : A→Site n) (s:Finset A):= s.image p
noncomputable def poly (p : Pairs A→Site n):Peak (Pairs A)⊕ (A × A) → Support n:= Sum.elim (fun i=> edges p i.val) (fun i=> {p (Sum.inl i.1),p (Sum.inr i.2)})
noncomputable def engineT (V:Matrix A A ℂ) (i : A× A):= V i.1 i.2 • (v (Sum.inr i.2)*v (Sum.inl i.1):EndA (Pairs A))
lemma engine_comm (V:Matrix A A ℂ)(i j:A × A): Commute (engineT V i) (engineT V j):=by
     apply timesComm; apply Commute.symm; apply timesComm; apply Commute.symm
     exact Commute.mul_left (swapsV ..) (swapsV ..) -- orientation check
lemma variesR (i:A) (V:Finset A)(h:i∈V): atom i∈region V:= Creek.marked _ _ h
lemma mono_in (i v:Finset A)(h:i⊆v): mono i∈region v:=by
     induction i using Finset.induction_on with
     | empty=> rw [mono_empty]; exact Subalgebra.one_mem _
     | insert j s hi ih=>
        obtain hv|hv:= mono_mul_sign {j} s (by simp [hi]:Disjoint {j} s); all_goals
           rw [disjUnion_eq_union,singleton_union,mono_single] at hv
           have hx:atom j*mono s∈region v:=(region v).mul_mem (variesR _ _ (h (mem_insert_self ..))) (ih ((subset_insert ..).trans h))
        · rw [← hv]; exact hx
        rw [hv] at hx; simpa using Subalgebra.neg_mem (region v) hx
lemma branch (F:Patio A)(p:A→Site n)(s:Peak A): light _ (interesting F s)∈ region (alphabet (p:=p) (edges p s.val)):= Subalgebra.smul_mem _ (mono_in _ _ fun j hj=> mem_filter.mpr ⟨mem_univ _,mem_image_of_mem _ hj⟩) _
noncomputable def mist (p: Pairs A→Site n)(F: Patio (Pairs A))(V:Matrix A A ℂ): Pads p (Peak (Pairs A)) (A×A):={
  source:= interesting F
  buys:=engineT V
  commute:= engine_comm V
  leaves:= poly p
  budget:=branch F p
  bill:=fun i=> Stays.pumps (gammaT (b:=Sum.inl i.1) (a:=Sum.inr i.2) (by simp [poly]) (by simp [poly])) _ }
lemma engineP (V:Matrix A A ℂ)(i:A×A):engineT V i 1=0:=by
   change V _ _ • vary _ (vary _ 1)=0; simp [vary_one]
lemma carry (s:Finset A)(x:Patio A)(h:Odd s.card): coef s (light _ x)=0:=by
     let y:= light A x; have he : grade y=y:=bright x; have ht: coef s y = -coef s y:=by
           nth_rw 1 [← he]; conv_lhs=> rw [← write y, map_sum,map_sum];
           rw [sum_eq_single s];
           · rw [map_smul, Grass.grade_mono, h.neg_one_pow, map_smul,map_smul,Grass.read]; simp
           · intro i _ hi; simp only [map_smul, Grass.grade_mono,Grass.read_other _ _ (Ne.symm hi),smul_zero]
           simp
     apply (mul_eq_zero.mp (show (2:ℂ)*coef s y=0 from by rw [two_mul, ← sub_neg_eq_add,← ht, sub_self])).resolve_left two_ne_zero
lemma lamp (X: Patio A)(h:coef ∅ X.val = 0): ∑ i:Peak A, interesting X i = X:=by
   apply Subtype.ext; change light _ _ = _; rw [map_sum];
   conv_rhs=> rw [← write X.val];
   symm; refine Eq.trans (Finset.sum_subset (s₁:=univ.filter fun i:Finset A=>Even (Finset.card i) ∧ 0 < Finset.card i) (f:=fun i=> coef i X.val • mono i) (subset_univ _) ?_).symm ?_
   · intro i hi ht; by_cases hx: i.Nonempty
     · rw [show coef i X.val=0 from carry i X (Nat.not_even_iff_odd.mp fun H=> ht (mem_filter.mpr ⟨hi,H,Finset.card_pos.mpr hx⟩)),zero_smul]
     rw [not_nonempty_iff_eq_empty.mp hx,h,zero_smul]
   rw [Finset.sum_subtype _ (p:=fun i: Finset A=> Even (Finset.card i) ∧ 0 < Finset.card i) (by simp)]; rfl
lemma pair_zero (X:Patio A) (i:Peak A) : (interesting X i)^2=0:=by
   rw [pow_two]; apply Subtype.ext; change (_ • mono i.val)*(_ • mono i.val)=0
   rw [smul_mul_assoc,mul_smul_comm, mono_mul_zero i.val i.val (by simp [(card_pos.mp i.2.2).ne_empty]),smul_zero,smul_zero]
lemma very (X:Patio A)(s: Peak A) : NormedSpace.exp (interesting X s) -1= interesting X s:=by
    let x:=interesting X s; have hh:light _ x*light _ x=0:=congr_arg Subtype.val (show interesting X s*_=0 from (pow_two (interesting X s)) ▸ pair_zero X s); refine Subtype.ext ?_; change light _ (exp x-1)=light _ x; rw [map_sub,Cove.light_exp,radius_two _ hh,map_one,add_sub_cancel_left]
-- nil contact exponent
lemma engine_sq (V:Matrix A A ℂ)(i:A × A):engineT V i^2=0:=by
    let I:=engineT V i; rw [pow_two]; let a:EndA (Pairs A):=v (.inl i.1); let b:EndA (Pairs A):=v (.inr i.2)
    have he(x: Pairs A): v x*v x=0:=by
           let V:=v x*v x; have hx: V + V = 0 := (eq_neg_iff_add_eq_zero).1 (circulate x x)
           have hh: (2:ℂ) • V = 0:= (two_smul ℂ V).trans hx
           exact (smul_eq_zero.mp hh).resolve_left two_ne_zero
    have hp:(b*a)*(b*a)=0:=by rw [mul_assoc, show a*(b*a)=b*a*a from (swapsV ..).eq,mul_assoc b a a,he _,mul_zero,mul_zero]; -- rewrite?
    change ((V i.1 i.2) • (b*a)) * ((V i.1 i.2) • (b*a))=_
    rw [spins,spinner,hp]; refine ContinuousLinearMap.ext (fun y=>?_); change V i.1 i.2 • V i.1 i.2 • (0:Alg (Pairs A))=0; simp
end YM.QCD.Nola
