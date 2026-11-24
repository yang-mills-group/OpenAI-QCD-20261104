import YM.QCD.Creek.Grade
/-! # the mixed wipe. no assumption of marginal positivity
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Function Finset Grass NormedSpace
open scoped Topology BigOperators ContDiff Matrix
variable {A B M:Type*} [Fintype A][Fintype B] [Fintype M]
variable [DecidableEq A][DecidableEq B]
-- SD two cases, act on common fine algebra
omit [DecidableEq B] in
lemma pulls (H:Matrix A A ℂ)(h:IsUnit H.det)(i:A)(x:Dirac A): seen H (psi i*x)=∑ a,H⁻¹ i a*seen H (vary (Sum.inr a) x):=by
  let u:A→ℂ:=Pi.single i (1:ℂ); have hm: straw u=psi i:=by simp [straw,u,Pi.single_apply,ite_smul, Pairs]
  have hz a: Matrix.vecMul u H⁻¹ a= H⁻¹ i a:=by simp [Matrix.vecMul,dotProduct,u,Pi.single_apply,ite_mul]
  rw [← hm,contracts _ h]; simp_rw [hz]
omit [DecidableEq A] [DecidableEq B] in
lemma pods (H:Matrix A A ℂ)(i:A): vary (Sum.inl i) (form H)=∑ j,H j i • bar j:=by
  classical
  unfold form; simp only [map_sum,map_smul]; refine sum_congr rfl fun j _=>?_ ; rw [sum_eq_single i]
  · rw [vary_mul,show vary (Sum.inl i) (bar j)=0 from vary_off _ _ (by simp),mul_zero,add_zero,psi,vary_self,one_mul]
  · intro k _ hk; rw [vary_mul,show vary (Sum.inl i) (psi k)=0 from vary_off _ _ (by simp [Ne.symm hk]), show vary (Sum.inl i) (bar j)=0 from vary_off _ _ (by simp)]; simp
  simp
omit [DecidableEq B] in
lemma brin_flow (H:Matrix A A ℂ)(i:A)(x:Dirac A): seen H (brin (fun j=> H j i)*x)= -seen H (vary (Sum.inl i) x):=by
  have hz:=integration (gauss H*x) (Sum.inl i)
  rw [vary_mul, show grade _=_ from gauss_plus H, gauss,varies_exp _ _ (form_plus H),pods,mul_assoc,map_add] at hz
  simp only [seen_apply, brin,gauss,eq_neg_of_add_eq_zero_left hz,mul_neg]
omit [DecidableEq B] in
lemma stems (H:Matrix A A ℂ)(h:IsUnit H.det)(i:A)(x:Dirac A): seen H (bar i*x) = ∑ j,(- H⁻¹ j i) * seen H (vary (Sum.inl j) x):=by
  have hh: bar i= ∑ j, H⁻¹ j i • brin (fun a=> H a j):=by
    unfold brin; simp only [smul_sum,smul_smul]; rw [sum_comm,sum_eq_single i]
    · rw [← sum_smul]; conv_rhs => rw [Finset.sum_congr rfl (g:=fun x=> H i x*H⁻¹ x i) (fun j _=> mul_comm ..)]
      rw [← Matrix.mul_apply,Matrix.mul_nonsing_inv _ h]; simp
    · intro j _ hj; rw [← sum_smul,sum_congr rfl (g:=fun a=> H j a*H⁻¹ a i) (fun a _=> mul_comm ..),← Matrix.mul_apply,Matrix.mul_nonsing_inv _ h]; simp [Matrix.one_apply,hj]
    simp
  rw [hh,sum_mul,map_sum]; apply sum_congr rfl; intro j _; rw [smul_mul_assoc,map_smul,brin_flow]; ring -- smul simp

variable (A B)
abbrev head : Pairs A ↪ Pairs (A⊕B):=Embedding.sumMap Embedding.inl Embedding.inl
abbrev tail : Pairs B ↪ Pairs (A⊕B):=Embedding.sumMap Embedding.inr Embedding.inr
omit [DecidableEq A] [DecidableEq B] in
lemma heights (i:Pairs A)(j:Pairs B): head A B i≠tail A B j:=by cases i <;> cases j <;> simp [head,tail]
-- merge

def wipeT (X: Matrix (Pairs A) (Pairs B) ℂ) : Matrix (Pairs (A⊕B)) (Pairs B) ℂ
 | Sum.inl (.inl i)=>X (.inl i)
 | Sum.inr (.inl i)=>X (.inr i)
 | Sum.inl (.inr j)=> (1 : Matrix (Pairs B) (Pairs B) ℂ) (.inl j)
 | Sum.inr (.inr j)=> (1 : Matrix (Pairs B) (Pairs B) ℂ) (.inr j)

def wipe (X: Matrix (Pairs A) (Pairs B) ℂ): Dirac (A⊕B) →ₐ[ℂ] Dirac B:=changeVars (wipeT A B X)
omit [DecidableEq A] in
lemma wiper (X: Matrix (Pairs A) (Pairs B) ℂ)(i : Pairs A) : wipe A B X (atom (head A B i))=∑ j, X i j • atom j :=by cases i <;> rw [wipe,change_atom] <;> rfl
omit [DecidableEq A] in
lemma tails (X: Matrix (Pairs A) (Pairs B) ℂ)(i: Pairs B): wipe A B X (atom (tail A B i))=atom i:=by
  rw [wipe,change_atom,show wipeT A B X (tail A B i)=(1: Matrix (Pairs B) (Pairs B) ℂ) i from by cases i <;> rfl]; simp [Matrix.one_apply,ite_smul]

variable {A B}
def drain (H:Matrix A A ℂ) : Dirac A →ₗ[ℂ] Dirac B:= ( (wipe A B 0).toLinearMap.comp (birth (pond (head A B) H)).toLinearMap).comp (near A B).toLinearMap

lemma nullVapply (H:Matrix A A ℂ)(B:Type*)[Fintype B]: birth (pond (head A B) H) 1=1:=powers _ _ (by simp only [pond,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.mul_apply]; simp [v,vary_one])

lemma paddle (H:Matrix A A ℂ)(i:A)(x:Dirac A): drain (B:=B) H (psi i*x)=∑ j,H i j • drain H (vary (Sum.inr j) x):=by
  let D:= birth (pond (head A B) H); let V:=wipe A B 0; let u:=near A B x; let y:= head A B (.inl i)
  change V (D ((near A B) _)) =_
  rw [map_mul,show near A B (psi i)=atom y from pass_psi .., show D (atom y*u)=(D*l y) u from rfl] -- may not match
  rw [show D*l y= l y*D+D*slotP _ H i from earnsP ..]; change V (l y (D u)+_) =_; rw [map_add]
  change V (atom y*D u)+ V (D (slotP (head A B) H i u))=_
  rw [map_mul,wiper, show ∑ j:Pairs B,(0:Matrix (Pairs A) (Pairs B) ℂ) (.inl i) j • atom j=0 by simp,zero_mul, zero_add,slotP,ContinuousLinearMap.sum_apply,map_sum,map_sum]
  apply sum_congr rfl; intro j _; rw [ContinuousLinearMap.smul_apply,map_smul,map_smul]; congr 1
  exact congr_arg (fun X=>V (D X)) (survives (head A B).injective (Sum.inr j) x)
lemma ford (H:Matrix A A ℂ)(i:A)(x:Dirac A): drain (B:=B) H (bar i*x)=∑ j,(-H j i) • drain H (vary (Sum.inl j) x):=by
  let D:= birth (pond (head A B) H); let V:=wipe A B 0; let u:=near A B x; let y:= head A B (.inr i)
  change V (D ((near A B) _)) =_
  rw [map_mul,show near A B (bar i)=atom y from pass_bar .., show D (atom y*u)=(D*l y) u from rfl] -- may not match
  rw [show D*l y= l y*D+D*slotM _ H i from earnsM ..]; change V (l y (D u)+_) =_; rw [map_add]
  change V (atom y*D u)+ V (D (slotM (head A B) H i u))=_
  rw [map_mul,wiper, show ∑ j:Pairs B,(0:Matrix (Pairs A) (Pairs B) ℂ) (.inr i) j • atom j=0 by simp,zero_mul, zero_add,slotM,ContinuousLinearMap.sum_apply,map_sum,map_sum]
  apply sum_congr rfl; intro j _; rw [ContinuousLinearMap.smul_apply,map_smul,map_smul]; congr 1
  exact congr_arg (fun X=>V (D X)) (survives (head A B).injective (Sum.inl j) x)

-- uniqueness against scalar source
lemma drained (H:Matrix A A ℂ)(h : IsUnit H.det)(x:Dirac A) : drain (B:=B) H⁻¹ x=seen H x • 1:=by
  let D:=drain (B:=B) H⁻¹
  have hi (u:List (Pairs A)): D (u.map atom).prod=seen H (u.map atom).prod • 1:=by
    suffices he : ∀ n:ℕ,∀ t: List (Pairs A),t.length≤ n→ D (t.map atom).prod=seen H (t.map atom).prod • 1 from he _ _ le_rfl
    intro n; induction n with
    | zero=> intro s hs; simp only [Nat.le_zero, List.length_eq_zero_iff] at hs; subst s; change D 1=seen H 1 • 1; change wipe A B 0 (birth _ ((near A B) 1))=_; rw [map_one,nullVapply,map_one,seen_one h,one_smul]
    | succ n ih=>
      -- use layers: derivative of list mon maps via lower_layer, induct all basis f. Sizes. 
      have hm (t: List (Pairs A)) (ht:t.length≤n) (i: Pairs A): D (vary i (t.map atom).prod) = seen H (vary i (t.map atom).prod) • 1:=by
        let x:= vary i (t.map atom).prod; change D x=seen H x • 1
        rw [← write x,map_sum,map_sum,sum_smul]; apply sum_congr rfl; intro y _; rw [map_smul,map_smul]
        by_cases hj : y.card = t.length-1
        · obtain ⟨w,-,-,hw⟩:= expression y
          have hv : D (mono y)=seen H (mono y) • 1:=by rw [hw]; simpa only [List.map_ofFn] using ih (List.ofFn w) (by rw [List.length_ofFn,hj]; omega)
          rw [hv,smul_smul,smul_eq_mul]
        rw [spectrum (lower_layer i t) _ hj]; simp
      intro s hs; cases s with
      | nil=> exact ih [] (by simp)
      | cons i s=>
        have ht : s.length ≤ n:=by simp only [List.length_cons] at hs; omega
        rcases i with i|i
        · change drain _ (psi i * (s.map atom).prod)=seen H (psi i*(s.map atom).prod) • _; rw [paddle,pulls _ h,sum_smul]; exact sum_congr rfl fun j _=> congr_arg (H⁻¹ i j • ·) (hm s ht (.inr j))|>.trans (smul_smul ..)
        change drain _ (bar i*(s.map atom).prod)=seen H (bar i*(s.map atom).prod) • _; rw [ford,stems _ h,sum_smul]; exact sum_congr rfl fun j _=>congr_arg (- H⁻¹ j i • ·) (hm s ht (.inl j))|>.trans (smul_smul ..)
  have hv s : D (mono s)= seen H (mono s) • 1:=by obtain ⟨w,-,-,hw⟩:= expression s; rw [hw]; simpa only [List.map_ofFn] using hi (List.ofFn w)
  change D x=_; rw [← write x,map_sum,map_sum,sum_smul]; simp_rw [map_smul,hv,smul_smul,smul_eq_mul]
end YM.QCD.Creek
