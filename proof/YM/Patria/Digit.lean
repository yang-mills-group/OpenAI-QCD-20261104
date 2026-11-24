import YM.Patria.Hollow
import YM.Poised.Cupcake
import YM.Planned.PRIMARY_INTEGRAL_295.Savings
/-! Exact marker motions -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice
open scoped ContDiff Topology BigOperators Classical
namespace Rolls
variable {X Y:Type}[AddCommGroup X][Module ℝ X][AddCommGroup Y][Module ℝ Y]
variable {u:Averaging}{m n M N k:ℕ} (v:Cover→X)(b:Cover)
variable (s:Signed)(l l':List PairS)(x:PairS)
def pivot (x:PairS):PairS:=(s.perm x.1,x.2)
lemma shifting (z:Sail)(l:List Axis) : ((l.map s.perm).flatMap (lanes (z∘s.perm.symm)))= (l.flatMap (lanes z)).map (pivot s):=by
    induction l with| nil=>rfl|cons i l h=> simp [List.flatMap_cons,h,lanes,pivot]
lemma spinning (f:Averaging) : List.Perm ((menu f).map (pivot s)) (menu (f.permute s)):=by -- f.permute order issue
    cases f with
    |none=>exact List.Perm.nil
    | some f=> change List.Perm (((List.finRange _).flatMap (lanes f)).map (pivot s)) ((List.finRange _).flatMap (lanes (f ∘ s.perm.symm))); rw [← shifting]; exact List.Perm.flatMap s.perm.map_finRange_perm fun _ _=> List.Perm.refl _ -- name
lemma forward (hp:l.Perm l'): rolls k M l v=rolls k M l' v:=by
    induction hp with| nil=>rfl| cons x h ih=> rw [rolls,rolls,ih]| swap x y l=> exact commute_axis ..| trans _ _ a b=>exact a.trans b
abbrev compact (n:ℕ)(s:Signed)(x:PairS) : Equiv.Perm (Fin n):= if s.flip x.1 then Fin.revPerm else Equiv.refl _
lemma striding (hm:Odd M)(i:Fin M) : s.act (stride x k i)=stride (pivot s x) k (compact M s x i):=by
    unfold stride compact pivot; dsimp only; have hz:= ((Step.vec_rotate (posDir x.1) s (R:=ℤ)).symm : _); unfold posDir Step.rotate at hz
    simp only [show ∀ (x:Cover) (n:ℤ),s.act (n • x)= n • s.act x from fun x n=>map_zsmul s.actEquiv n x]
    cases h:s.flip x.1
    · rw [show s.act (Lattice.step x.1:Cover)=Lattice.step (s.perm x.1) from (by simpa [Step.vec,h] using hz)]; rw [if_neg (by decide)]; rfl
    rw [show s.act (Lattice.step x.1:Cover)=-Lattice.step (s.perm x.1) from (by simpa [Step.vec,h] using hz), smul_neg]; apply congr_arg; simp only [h,↓reduceIte]; rw [← neg_smul]; apply congr_arg (fun z:ℤ=> z • (Lattice.step (s.perm x.1):Cover)); obtain ⟨q,hq⟩:= hm; change _= (i.rev.val:ℤ)-centre M; unfold centre; rw [Fin.val_rev]; omega
lemma portrait (hm:Odd M) (w:Cover→X)(h:∀ b,v b=w (s.act b)) : rolls k M l v b=rolls k M (l.map (pivot s)) w (s.act b):=by
    induction l generalizing b with
    |nil=> exact h _
    |cons i l ih=>
       simp_rw [List.map_cons,rolls, sumG]; apply congr_arg; rw [← Equiv.sum_comp (compact M s i) (g:=fun x=> rolls k M (l.map (pivot s)) w (s.act b+stride (pivot s i) k x))]; apply sum_congr rfl; intro j _; rw [ih,Signed.act_add,striding _ _ hm]
lemma stage_perm (F:X→ₗ[ℝ]Y)(w:Cover→Y)(u:Averaging)(h:∀ p,F (v p)=w (s.act p))(hm:Odd M): F (Averaging.filter u M v 0)= Averaging.filter (Averaging.permute s u) M w 0:=by
    rw [roles,rollLinear,roles,← forward _ _ _ (spinning s u)]; exact (portrait (fun i=> F (v i)) 0 s _ hm w h).trans (by rw [Signed.act_zero]) -- sig
-- compiler bounds and probability coupons
lemma length_menu (u:Averaging) : (menu u).length ≤ 28:=by
    cases u with | none=> simp [menu]|some f=>
      have hf (v:List Axis): (v.flatMap (lanes f)).length ≤ 7*v.length:=by
         induction v with|nil=> simp | cons i l ih=> simp only [List.flatMap_cons,List.length_append,lanes,List.length_cons,List.length_replicate]; have ht: (l.flatMap (fun a=>(a,1)::List.replicate (f a).val (a,2))).length≤7*l.length:= ih; have he:= (f i).isLt; omega
      exact (hf (List.finRange 4)).trans_eq (by simp)
lemma widths_menu (u:Averaging):∀ p∈menu u,p.2 ≤ 2:=by
    cases u with
    | none=> simp [menu]
    | some f=>
       intro p hp; obtain ⟨i,-,hx|hx⟩ : ∃ i∈List.finRange 4,p=(i,1) ∨ p∈List.replicate (f i).val (i,2):= by simpa only [lanes,List.mem_cons] using! (List.mem_flatMap.mp hp) -- cons_iff
       · simp [hx]
       rw [List.mem_replicate] at hx; simp [hx.2]
open Laurent
lemma widths (h : x.2 ≤2)(i:Fin M) : Laurent.size (stride x 1 i) ≤ 2*M:=by
    have he (x:ℤ)(y:Cover) : size (x • y)=x.natAbs*size y:=by simp [size,Finset.mul_sum,Int.natAbs_mul]
    rw [stride,he,he,Poised.Chute.step_sway, mul_one,one_mul,Int.natAbs_natCast]; refine Nat.mul_le_mul h ?_; unfold centre; omega
lemma ladder (k:ℕ)(hM:m>0)(hv:∀ p∈l,p.2≤2):∃ (I:Type)(_ :Fintype I)(_ :Nonempty I)(P:I→ℝ)(g:I→ Cover),(∀ i,0≤ P i) ∧ (∑ i,P i)=1∧ (∀ i,Laurent.size (g i) ≤ l.length*(2*m)) ∧ ∀ (v:Cover→X)(b:Cover), rolls 1 m l v b= ∑ i,P i • v (b+g i):=by -- X not in statement? X template yes
    induction l with
    |nil=> refine ⟨Unit,inferInstance,inferInstance,fun _=>1,fun _=>0,fun i=>zero_le_one,by simp,fun i=>?_,fun i b=>?_⟩; · simp [Laurent.size]
           simp [rolls]
    |cons i l ih=>
       obtain ⟨J,hJ,hN,P,g,h0,h1,h2,hZ⟩:= ih (fun p hp=> hv p (List.mem_cons_of_mem _ hp)) -- name collision rename
       let L:= Fin m×J; haveI : NeZero m:= ⟨hM.ne'⟩; let Z : ℝ:=(m:ℝ)⁻¹; let p(v:L):=Z*P v.2; let w(v:L):= stride i 1 v.1+g v.2; have hz:0 < Z:= inv_pos.mpr (Nat.cast_pos.mpr hM)
       refine ⟨L,inferInstance,inferInstance,p,w,fun i=>mul_nonneg hz.le (h0 _), ?_,fun j=>?_,fun v b=>?_⟩
       · change (∑ i:Fin m×J,Z*P i.2)=_; rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum,h1,mul_one,sum_const, card_univ, Fintype.card_fin,nsmul_eq_mul]; exact mul_inv_cancel₀ ((Nat.cast_pos.mpr hM): (0:ℝ)<(m:ℝ)).ne'
       · have hR : i.2 ≤2:=by apply hv _ (by simp)
         exact (size_add ..).trans (le_trans (add_le_add (widths i hR j.1) (h2 j.2)) (show _≤_ from by rw [List.length_cons,add_mul,one_mul,Nat.add_comm]))
       rw [rolls,sumG,Fintype.sum_prod_type]; simp_rw [hZ,Finset.smul_sum,p,w, smul_smul,add_assoc]; rfl
end Rolls
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Rolls.ladder
