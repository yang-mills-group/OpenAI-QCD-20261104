import YM.MassiveQCD.Mayer.Analytic
import YM.Push.ABSOLUTE_SUMS.Array
/-! # Euler rays list-price receipts
 Encode the exponential of new columns, without smuggling in uncounted powers.
 Every nonempty list is an occurrence of ≥ double the power of its tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Analysis.Many
open YM.RG Push.AbsoluteSums
open Function Filter Topology Finset NormedSpace Set Metric
open scoped ENNReal NNReal BigOperators Classical
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
-- Nontrivial if equating exp. Laws assume.
abbrev Rays := List ℕ
def branch (n:ℕ) (x:A):= (-coeffM (n+2)) • x^(n+2)
def grow (x:A) : Rays→A
 | []=>x
 | n::l=> branch n (grow x l)
def tier : Rays→ℕ | []=>1 | n::l=>(n+2)*tier l
def wagon (n:ℕ):ℝ := (1/4:ℝ)^(n+1)
noncomputable def vigor : Rays→ℝ
 | [] => 1
 | n::l=> wagon n*vigor l
lemma tack (l:Rays) : tier l≥1∧0<vigor l ∧vigor l≤1:=by
    induction l with
    | nil=> exact ⟨le_rfl,zero_lt_one,le_rfl⟩
    | cons n l ih=> exact ⟨Nat.le_trans ih.1 (Nat.le_mul_of_pos_left _ (by omega)),mul_pos (show 0<wagon n from by unfold wagon; positivity) ih.2.1,mul_le_one₀ (pow_le_one₀ (by norm_num) (by norm_num)) ih.2.1.le ih.2.2⟩
noncomputable def twins : Unit⊕ Rays × ℕ ≃ Rays :=
   { toFun:=Sum.elim (fun _=>[]) fun (x,y)=> y::x
     invFun:=fun | []=>.inl ()| n::l=> .inr (l,n)
     left_inv:=by rintro (⟨⟩|⟨w,k⟩) <;> rfl
     right_inv:=by intro s; cases s <;> rfl }
lemma summit : SumBudget wagon (1/2):=by
    apply budget_loosen (C:=1/4*(1-1/4)⁻¹) ?_ (by norm_num); unfold wagon; simp_rw [pow_succ']; exact budget_geometric (by norm_num) (by norm_num) (by norm_num)
lemma budget_join {X Y:Type*}{f:X→ℝ}{g:Y→ℝ}{a b:ℝ}(h:SumBudget f a)(he:SumBudget g b): SumBudget (Sum.elim f g) (a+b):=by
    have hx:= HasSum.sum (f:=Sum.elim f g) h.2.1.hasSum he.2.1.hasSum
    refine ⟨fun i=>?_,hx.summable,hx.tsum_eq.trans_le (add_le_add h.2.2 he.2.2)⟩; cases i with| inl _=> exact h.1 _ | inr _=> exact he.1 _
lemma purse : SumBudget vigor 2:=by
    let F (n:ℕ)(l:Rays):= if l.length≤n then vigor l else 0
    have he n : SumBudget (F n) 2:=by
       induction n with
       | zero=>
          apply budget_of_sum (fun i=> ite_nonneg (tack i).2.1.le le_rfl); intro s; by_cases h: ([]:Rays)∈s
          · rw [sum_eq_single_of_mem [] h]; · simp [vigor]
            intro i _ hi; simp [hi]
          rw [sum_eq_zero]; · norm_num
          intro i hi; simp [show i ≠ [] from ne_of_mem_of_not_mem hi h]
       | succ n ih=>
          have ht:= budget_prod ih summit
          have hx : SumBudget (fun i=> F (n+1) (twins i)) (1+2*(1/2)):=by
              rw [show (fun i=> F (n+1) (twins i)) = Sum.elim (fun (_:Unit)=> (1:ℝ)) (fun i : Rays × ℕ=> F n i.1*wagon i.2) from ?_]; apply budget_join -- find
              · apply budget_finite <;> simp
              · exact ht
              funext i; cases i with
              | inl w=>simp [twins,F,vigor]
              | inr v=> change F (n+1) (v.2::v.1)=F n v.1*wagon v.2; unfold F; split_ifs with h₁ h₂
                        · exact mul_comm ..
                        · simp only [List.length_cons,add_le_add_iff_right] at h₁; omega
                        · simp only [List.length_cons,add_le_add_iff_right] at *; omega
                        rw [zero_mul]
          have hh:= budget_pull twins.symm twins.symm.injective hx; simp only [Equiv.apply_symm_apply] at hh; exact budget_loosen hh (by norm_num)
    refine budget_of_sum (fun i=>(tack i).2.1.le) ?_; intro s; rw [sum_congr rfl (g:= F (s.sup List.length)) (fun i hi=> by unfold F; rw [if_pos (le_sup (f:=List.length) hi)])]; exact budget_sum (he (s.sup List.length)) s
-- telescoping all frequencies. charge separately at λ evaluated values, no analyticity assertion outside mask
variable {x:A}
lemma aliveM {l : Rays}(h:‖grow x l‖<1): HasSum (fun n=>grow x (n::l)) (grow x l-logM (grow x l)) :=by
    let u:=grow x l; let f n:= coeffM n • u^n; have he: Summable f:= (logs (x:=u) h).of_norm
    have hh : Summable (fun i=>f (i+2)):= (summable_nat_add_iff 2).2 he; refine HasSum.congr_fun (f:=fun n=> -f (n+2)) ?_ (fun n=>?_)
    · have hx : logM u= u+∑' i,f (i+2) := Eq.symm (by change _=∑' i,f i; simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, show f 0=0 by simp [f,coeffM], show f 1=u by simp [f,coeffM,alternate], zero_add] using he.sum_add_tsum_nat_add 2) -- danger simp order
      change HasSum _ (u-logM u); rw [hx, show u-(u+∑' i,f (i+2))= -(∑' i,f (i+2)) from by abel]; exact hh.hasSum.neg
    exact neg_smul ..
-- gather ALL rays
lemma blooming (hp:Summable (grow x)) (hh:Summable fun i=> logM (grow x i)) (ht:∀ i, ‖grow x i‖<1) : HasSum (fun i=> logM (grow x i)) x := by
    let F:= grow x; have hM : Summable (fun i:Rays × ℕ=> grow x (i.2:: i.1)):= hp.comp_injective (twins.injective.comp Sum.inr_injective)
    let L i:=logM (grow x i); have hx:= (hp.hasSum.sub hh.hasSum); let s:=∑' i,F i; let X:=∑' i,L i
    have he : HasSum (fun i:Rays × ℕ=>F (i.2:: i.1)) (s-X):=by
         suffices hg : ∑' i:Rays × ℕ, (F (i.2:: i.1)) = s-X from hg ▸ hM.hasSum
         exact hM.tsum_prod.trans ((tsum_congr (fun i=> (aliveM (ht i)).tsum_eq)).trans hx.tsum_eq)
    have hU: HasSum (F ∘ twins) (x+(s-X)):= by
         refine HasSum.sum ?_ he
         change HasSum (fun _:Unit=>x) x
         convert hasSum_fintype (fun _:Unit=>x) using 1; simp
    have hV := (twins.hasSum_iff).mp hU|>.tsum_eq; change s=x+(s-X) at hV; have h0:X=x:=by
         apply add_left_cancel (a:=s); calc
           _=(x+(s-X))+X:=congr_arg (·+X) hV
           _=s+x:=by abel
    nth_rw 2 [← h0]; exact hh.hasSum

end YM.MassiveQCD.Analysis.Many
