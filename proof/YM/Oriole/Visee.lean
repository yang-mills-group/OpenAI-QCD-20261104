import YM.Oriole.Hoop
/-! Averaging/shift commutation.Exact telescoping. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Rolls
open Function Lattice RG Filter Finset
open scoped BigOperators Classical
variable {X Y: Type} [AddCommGroup X][Module ℝ X][AddCommGroup Y][Module ℝ Y]
variable {c f: Side}{n k:ℕ}(F:Cover→X)
local notation "L" a:arg=> Lattice.step (S:=ℤ) a
variable (a:Axis)(b:Cover)
lemma pledge (M:ℕ)(u:Averaging): Averaging.filter u M F b= rolls 1 M (menu u) F b:=congr_fun (roles ..) b
local notation "iM"=>MassFields.isotropic
local notation "aM"=>MassFields.atVector a
lemma collar : List.Perm (menu iM) ((a,2)::menu aM):=by
     -- decide? kernel via Lining.Gr.Compare. permitted.Fit DecEq. finite reduction #4 whnf avoid huge.
     fin_cases a <;> decide
lemma grantR (v:Averaging):let Y(x):=F (x + L a)-F (x-L a); let Q:= Averaging.filter v n F; Averaging.filter v n Y b= Q (b+L a)-Q (b-L a):=by
     intro Y Q; let s:= menu v; rw [pledge]; let A(x:Cover):= F (x+L a); let B(x:Cover):=F (x-L a); have h:Y=A + (-B):= funext fun x=> sub_eq_add_neg ..; rw[h,training,Pi.add_apply]; have hv(x:Cover):rolls 1 n s (-B) x = - rolls 1 n s B x:= (show _=_ from (rollLinear (v:=B) (l:=s) (M:=n) (k:=1) (X:=X) (Y:=X) x (-LinearMap.id)).symm) -- sig
     rw [show rolls 1 n _ (-B) b= _ from hv b, driftRoll F b 1 s]; rw [show rolls 1 n s B b=(rolls 1 n s F (b+ -L a)) from ?_]; swap
     · unfold B; simp_rw [sub_eq_add_neg]; apply driftRoll
     unfold Q; rw [pledge,pledge]; simp only [sub_eq_add_neg]; rfl
lemma perF (M:ℕ): Averaging.filter iM M F b = glance (a,2) 1 M (Averaging.filter aM M F) b:=by rw[roles,roles,(forward F _ _ (collar a)),rolls] -- sig
lemma prec (M:ℕ)(h: Odd M) : (∑ i:Fin M, (F (b+stride (a,2) 1 i+L a) - F (b+stride (a,2) 1 i-L a))) = F (b + M • L a)-F (b- M • L a):=by
     let F'(i:ℕ):= F (b + (-(M:ℤ)+2*(i:ℤ)) • L a)
     have he0 : F' 0= F (b- M • L a):=by simp [F',sub_eq_add_neg]
     have heM : F' M= F (b + M • L a):=by unfold F'; rw [show -(M:ℤ)+ 2*M=M from by ring]; simp -- lemma?
     have ht(k:ℕ): (∑ i∈ Finset.range k,(F' (i+1)- F' i))= F' k-F' 0:=by
          induction k with|zero=> simp|succ k ih=> rw [Finset.sum_range_succ,ih]; abel
     have hh(i:Fin M): F (b+stride (a,2) 1 i+L a)-F (b+stride (a,2) 1 i-L a)= F' (i.val+1)-F' i.val:=by
          obtain ⟨q,hq⟩:=h; unfold F'; have hx:(M-1)/2=q:=by omega ;
          refine congr_arg₂ (·-·) (congr_arg F ?_) (congr_arg F ?_)
          · unfold stride; change b+ (((1*2:ℕ):ℤ) • (((i.val:ℤ)-centre M) • L a))+L a = _; rw [← mul_smul,add_assoc]; unfold centre; rw[hx]; apply congr_arg; nth_rw 2 [← one_smul ℤ (L a)]; rw [← add_smul]; congr 1; omega
          unfold stride; change b+ (((1*2:ℕ):ℤ) • (((i.val:ℤ)-centre M) • L a))-L a= _; rw [← mul_smul,add_sub_assoc]; apply congr_arg; unfold centre; rw [hx]; nth_rw 2[← one_smul ℤ (L a)]; rw [← sub_smul]; congr 1; omega
     simp_rw [hh]; rw [←he0,←heM]; refine Eq.trans (?_: _= (∑ i∈Finset.range M,_)) (ht M); rw [←Fin.sum_univ_eq_sum_range]
noncomputable def nick (C:ℝ)(a:Axis)(Z:Cover→X)(v:Cover) := (C/2) • (Z (v+Lattice.step a)-Z (v - Lattice.step a))
lemma equalR (C:ℝ)(h:Odd n) : Averaging.filter iM n (nick C a F) b= ((C / (n:ℝ))/2) • (Averaging.filter aM n F (b+n • L a)- Averaging.filter aM n F (b - n • L a)):=by
     rw[perF (a:=a),sumG]; let v(x):= F (x+ L a) - F (x - L a); let g(x:Cover):= Averaging.filter aM n F x; let f(x):=g (x+ L a)-g (x - L a); let L':X→ₗ[ℝ]X:= (C/2) • LinearMap.id; have ht(x):Averaging.filter aM n (nick C a F) x=(C/2) • f x:=by
          have h:(C/2) • f x= L' (Averaging.filter aM n v x):= congr_arg L' (grantR F a x aM).symm; rw [h,roles,roles]; exact (rollLinear (v:=v) (l:=menu aM) (M:=n) (k:=1) x L').symm
     simp_rw [ht]; rw [←smul_sum]; have he : (∑ i: Fin n, f (b+stride (a,2) 1 i)) = _:= prec g a b n h; rw [he,smul_smul]; refine congr_arg₂ HSMul.hSMul (by ring) rfl
omit [AddCommGroup Y] [Module ℝ Y] in
lemma accumulate (t: Finset Y)(f:Y→ Cover →X)(k:ℕ)(u:Averaging): Averaging.filter u k (∑ i∈t,f i) b=∑ i∈t,Averaging.filter u k (f i) b:=by
     induction t using Finset.induction_on with
     | empty=> rw[sum_empty,sum_empty,roles]; let Lc:X→ₗ[ℝ] X:=0; exact (rollLinear (v:=fun _=>0) (l:=menu u) (M:=k) (k:=1) b Lc).symm -- type
     | @insert i t h ih=> rw [sum_insert ‹_›, sum_insert ‹_›,← ih]; rw [roles,training,roles,roles]; rfl
open Depth
variable {S:Scheme} {i:ℕ}
lemma tollR (i:ℕ): S.spacing i >0:=by unfold Scheme.spacing; positivity
abbrev exchanging (S:Scheme)(i:ℕ)(F:Cover→X)(b:Cover):= F (ratioTo S n i • b)
lemma stepwise (x:Cover)(h:i≤ n): Averaging.filter iM (ratioTo S n i) (nick (S.spacing n)⁻¹ a F) (ratioTo S n i • x)= ((S.spacing i)⁻¹/2) • (Averaging.filter aM (ratioTo S n i) F (ratioTo S n i • (x+L a))-Averaging.filter aM (ratioTo S n i) F (ratioTo S n i • (x-L a))):=by
      rw [equalR _ _ _ _ (odd_to h),smul_add,smul_sub (ratioTo S n i) x]; congr 2; unfold Scheme.spacing; rw [factorize h,Nat.cast_mul]; field_simp [(Nat.cast_ne_zero.mpr (odd_to h|>.pos.ne') : (ratioTo S n i:ℝ)≠0)]
open QCD QCD.Lat
variable (A:Run S n c 6)(p:Cover→ Insertion (S.side c n) 6)(W:Averaging)(q r:Cover→ Insertion (S.side c n) 6)
lemma treadM (b:Cover) : Depth.trolley A (p+q) W i b=Depth.trolley A p W i b+Depth.trolley A q W i b:=by unfold trolley Depth.visitor; rw [roles,training,Pi.add_apply,mul_add,map_add,roles,roles]
lemma scopeY (t:ℂ)(b:Cover): Depth.trolley A (t • p) W i b=t • trolley A p W i b:=by
      unfold trolley Depth.visitor; let B:= Insertion (S.side c n) 6; let Lc:B→ₗ[ℝ] B:=(t • (LinearMap.id (R:=ℂ) (M:=Insertion (S.side c n) 6))).restrictScalars ℝ; rw[roles,roles,show rolls 1 _ _ (t • p) _= t • rolls 1 _ _ p _ from (rollLinear (v:=p) (M:=ratioTo S n i) (k:=1) (l:=menu W) (ratioTo S n i • b) Lc).symm,mul_smul_comm,map_smul]
lemma honest (x:Cover) (hi: i≤ n): trolley A (nick (S.spacing n)⁻¹ a p) iM i x= ((S.spacing i)⁻¹/2) • (trolley A p aM i (x+L a)-trolley A p aM i (x-L a)):=by
     unfold trolley Depth.visitor; rw[stepwise _ _ x hi]; rw [mul_smul_comm,mul_sub,← map_sub]; exact map_smul ((S.toStop c A.β A.w n i (F:=6)).restrictScalars ℝ) _ _
lemma silver (u:ℕ): ratioTo S u 0=(S.ratio u).val:= by unfold ratioTo; change _/ (1:ℕ)= _; rw[Nat.div_one] -- spacing
end YM.Massive.Patria.Rolls
#print axioms YM.Massive.Patria.Rolls.stepwise
#print axioms YM.Massive.Patria.Rolls.accumulate
#print axioms YM.Massive.Patria.Rolls.honest
