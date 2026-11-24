import YM.Avian.Skein
import YM.Shade.Alpine
/-! family stencil averages. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Rolls
open Function Filter Lattice Wilson RG
open scoped Topology BigOperators ContDiff Matrix Classical
open QCD QCD.Lat Intag Patria.Depth
private def ticket (i:ℕ):Fin 7:=⟨3-i,by omega⟩
def paysS (l:List Axis): Averaging:= .some fun i=> ticket (l.count i)
lemma pays_rotate (l:List Axis)(s:Signed): Averaging.permute s (paysS l)=paysS (l.map s.perm):=by
    apply Option.some.injEq ..|>.mpr; funext i; apply congr_arg ticket; change l.count (s.perm.symm i)=List.count i (l.map s.perm); induction l with
    | nil=>rfl
    | cons j l ih=>by_cases h:s.perm j=i
                   · have he: j=s.perm.symm i:= s.perm.eq_symm_apply.mpr h; simp [List.count_cons, h,beq_iff_eq,ih,he] -- simp may fail
                   have he: ¬ j=s.perm.symm i:= h ∘ s.perm.eq_symm_apply.mp; simp[List.count_cons, beq_iff_eq, Ne.symm h,Ne.symm he,ih,h,he]
lemma pais (l l':List Axis)(h:l.Perm l'):paysS l=paysS l':= congr_arg Option.some (funext fun i=> congr_arg ticket (h.count_eq i))
-- actual choices R2 orientation
noncomputable abbrev shelV (a:Axis):= paysS [a]
noncomputable abbrev shelS (a b:Axis):= paysS [a,b]
noncomputable abbrev shelC(a b c:Axis):=paysS [a,b,c]
lemma signP(a b:Axis) : shelS a b=shelS b a:=pais _ _ (List.Perm.swap b a [])
-- Avoid heavy `decide`. through permutation
abbrev Goes (a:Axis)(u v:Averaging):Prop:= (menu v).Perm ((a,2)::menu u)
lemma can_go(a:Axis)(l:List Axis)(h:l.length<3): Goes a (paysS (a::l)) (paysS l):=by
    let x(i:Axis):= ticket (l.count i); let y(i:Axis):= ticket ((a::l).count i)
    have he(k:Axis)(hn:k≠a):y k=x k:=by unfold y x; simp [Ne.symm hn, hn]
    have hp: (x a).val=(y a).val+1:=by
          let s:= l.count a; have hs:s <3:= lt_of_le_of_lt (List.count_le_length ..) h; unfold x y ticket; simp only [List.count_cons_self]; change 3-s=3-(s+1)+1; omega
    change List.Perm ((List.finRange 4).flatMap (lanes x)) ((a,2)::(List.finRange 4).flatMap (lanes y))
    obtain ⟨s,t,ht⟩:= List.append_of_mem (List.mem_finRange a); have hh: List.Nodup (s++a::t):= by rw[← ht]; exact List.nodup_finRange _
    have hS: a∉ s:=fun ha=> (List.disjoint_of_nodup_append hh) ha (List.mem_cons_self ..)
    have hT: a∉ t:= (List.nodup_cons.mp ((List.nodup_append.mp hh).2.1)).1
    have hb(s: List Axis)(hs:a∉s): s.flatMap (lanes x)= s.flatMap (lanes y):=by induction s with|nil=>rfl|cons b l ih=> have h1:y b=x b:=he _ (by simp at hs; exact Ne.symm hs.1); rw [List.flatMap_cons,List.flatMap_cons,ih, show lanes x b=lanes y b from by unfold lanes; rw[h1]]; exact fun h=>hs (List.mem_cons_of_mem _ h)
    rw [ht,List.flatMap_append,List.flatMap_append,List.flatMap_cons,List.flatMap_cons,hb s hS, hb t hT]; have hz:(lanes x a).Perm ((a,2):: lanes y a):=by unfold lanes; rw [hp,List.replicate_succ]; exact List.Perm.swap ..
    exact (List.Perm.append_left _ (List.Perm.append_right _ hz)).trans (List.perm_middle ..) -- order
variable {M: Type} [AddCommGroup M] [Module ℝ M] (F:Cover → M)(a:Axis)(b:Cover)(U V:Averaging)(h:Goes a U V)
local notation "e"=> Lattice.step a
variable {n i:ℕ}
include h
lemma earnings (C:ℝ)(hn:Odd n) : Averaging.filter V n (nick C a F) b= ((C / (n:ℝ))/2) • (Averaging.filter U n F (b+n • e)- Averaging.filter U n F (b - n • e)):=by
     rw [roles,(forward _ _ _ h),rolls,←roles,sumG]; let v(x):= F (x+ e) - F (x - e); let g(x:Cover):= Averaging.filter U n F x; let f(x):=g (x+ e)-g (x - e); let L':M→ₗ[ℝ]M:= (C/2) • LinearMap.id; have ht(x):Averaging.filter U n (nick C a F) x=(C/2) • f x:=by
          have h:(C/2) • f x= L' (Averaging.filter U n v x):= congr_arg L' (grantR F a x U).symm; rw [h,roles,roles]; exact (rollLinear (v:=v) (l:=menu U) (M:=n) (k:=1) x L').symm
     simp_rw [ht]; rw [←Finset.smul_sum]; have he : (∑ i: Fin n, f (b+stride (a,2) 1 i)) = _:= prec g a b n hn; rw [he,smul_smul]; refine congr_arg₂ HSMul.hSMul (by ring) rfl
variable {S:Scheme}
lemma walks (x:Cover)(ht:i ≤ n): Averaging.filter V (ratioTo S n i) (nick (S.spacing n)⁻¹ a F) (ratioTo S n i • x)= ((S.spacing i)⁻¹/2) • (Averaging.filter U (ratioTo S n i) F (ratioTo S n i • (x+e))-Averaging.filter U (ratioTo S n i) F (ratioTo S n i • (x-e))):=by
      rw [earnings _ _ _ U _ h _ (odd_to ht),smul_add,smul_sub (ratioTo S n i) x]; congr 2; unfold Scheme.spacing; rw [factorize ht,Nat.cast_mul]; field_simp [(Nat.cast_ne_zero.mpr (odd_to ht|>.pos.ne') : (ratioTo S n i:ℝ)≠0)] -- namespace
variable {c:Side}(A:Run S n c 6)(p:Cover→Insertion (S.side c n) 6)
lemma stoic (x:Cover) (hi: i≤ n): trolley A (nick (S.spacing n)⁻¹ a p) V i x= ((S.spacing i)⁻¹/2) • (trolley A p U i (x+e)-trolley A p U i (x-e)):=by
     unfold trolley Depth.visitor; rw[walks _ _ U _ h x hi]; rw [mul_smul_comm,mul_sub,← map_sub]; exact map_smul ((S.toStop c A.β A.w n i (F:=6)).restrictScalars ℝ) _ _
end YM.Massive.Patria.Rolls
#print axioms YM.Massive.Patria.Rolls.stoic
