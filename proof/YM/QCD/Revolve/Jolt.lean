import YM.QCD.Sparks.Raise

/-! # ambiguity of Spin and chirality at orientation -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Function Lattice Wilson Kit Pine Cost
open scoped Matrix Matrix.Norms.L2Operator ContDiff Kronecker
variable {A B: Spike}{s:Signed}

lemma lesser (h:Swing s A) (he:Swing s B)(i:Axis):Commute (star B*A) (gamma i):=by
  let Y:= if s.flip i then -gamma (s.perm i) else gamma (s.perm i)
  have hA:A*gamma i= Y*A:=h.sends _; have hB:B*gamma i=Y*B:=he.sends _
  have hh:=congr_arg star hB; rw [star_mul, star_mul, gamma_star, show star Y= Y from ?_] at hh; swap; · unfold Y; split <;> simp
  unfold Commute SemiconjBy; rw [Matrix.mul_assoc,hA, ← Matrix.mul_assoc,← hh, Matrix.mul_assoc]

private lemma y12 : sx*sy=Complex.I • sz:=by ext i j; fin_cases i <;> fin_cases j <;> simp [sx,sy,sz,Matrix.mul_apply,Fin.sum_univ_succ]
private lemma γ : gamma 0*gamma 1*gamma 2*gamma 3= -g5:=by
  rw [show gamma 0=sx ⊗ₖ (1:Pauli) from rfl, show gamma 1=sy ⊗ₖ sx from rfl, show gamma 2=sy ⊗ₖ sy from rfl, show gamma 3=sy ⊗ₖ sz from rfl]; unfold g5; rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,one_mul,y12, Matrix.mul_assoc _ sy,yy,mul_one,Matrix.smul_mul,zz, Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,Complex.I_mul_I, neg_one_smul]
lemma edge_ev (hp : ∀ i,Commute A (gamma i)) : Commute A g5:=by
  have he:=(((hp 0).mul_right (hp 1)).mul_right (hp 2)).mul_right (hp 3); rw [γ] at he; simpa only [neg_neg] using he.neg_right
-- gamma1*gamma2=i* id kron sz -> diagonal. Need common scalar across both dims. general matrix diagonal forms.
private lemma ζ : gamma 1*gamma 2= Complex.I • ((1:Pauli) ⊗ₖ sz) :=by change (sy ⊗ₖ sx)*(sy⊗ₖsy)=_; rw [← Matrix.mul_kronecker_mul, yy,y12,Matrix.kronecker_smul]
private lemma polar (hp:∀ i,Commute A (gamma i)):Commute A ((1:Pauli) ⊗ₖ sz):=by
  have h:=(hp 1).mul_right (hp 2); rw [ζ] at h; have he:=h.smul_right Complex.I⁻¹; rw [inv_smul_smul₀ Complex.I_ne_zero] at he; exact he

private def price₅ (a : Fin 2):ℂ:= if a=0 then 1 else -1
private lemma slash₅ : g5=Matrix.diagonal (fun i=>price₅ i.1):=by
  ext ⟨i,a⟩ ⟨j,b⟩; fin_cases i <;> fin_cases j <;> simp [g5,sz,Matrix.diagonal_apply, Matrix.one_apply,price₅, neg_mul,apply_ite Neg.neg]
private lemma sash : (1:Pauli)⊗ₖsz=Matrix.diagonal (fun i=>price₅ i.2):=by
  ext ⟨a,i⟩ ⟨b,j⟩; fin_cases i <;> fin_cases j <;> simp [sz,Matrix.diagonal_apply, Matrix.one_apply,price₅, ite_mul]
  split <;> simp
private lemma fire (v : Pinor→Fin 2)(h : Commute A (Matrix.diagonal (price₅∘v)))(i j:Pinor)(hh:v i ≠ v j): A i j=0:=by
  have he:=Matrix.ext_iff.mpr h.eq i j; rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  by_contra ht; apply hh; have hw: Injective price₅:=by intro u v; fin_cases u <;> fin_cases v <;> norm_num [price₅]; -- invite
  apply hw; apply mul_right_cancel₀ ht; exact he.symm.trans (mul_comm ..)
private lemma trail_diag (hp:∀ i,Commute A (gamma i)): A=Matrix.diagonal (fun i=>A i i):=by
  ext ⟨i,j⟩ ⟨k,l⟩; rw [Matrix.diagonal_apply]; split_ifs with ht; · rw [Prod.mk.injEq] at ht; rw [ht.1,ht.2]
  have he:=edge_ev hp; have hk:=polar hp; rw [slash₅] at he; rw [sash] at hk
  by_cases h:i=k; · subst k; apply fire Prod.snd hk; exact fun w=> ht (Prod.ext rfl w)
  exact fire Prod.fst he _ _ h
private lemma agrees (hp:∀ i,Commute A (gamma i))(a : Axis)(v w:Pinor)(he:gamma a v w≠0): A v v=A w w:=by
  have ht:=hp a|>.eq; have hh:=trail_diag hp; rw [hh] at ht
  have hx:=Matrix.ext_iff.mpr ht v w; rw [Matrix.mul_diagonal,Matrix.diagonal_mul] at hx; exact mul_right_cancel₀ he (hx.trans (mul_comm ..))
lemma scalar_spin (h:∀ i,Commute A (gamma i)): A=A (0,0) (0,0) • (1:Spike):=by
  have hh (i:Pinor) : A i i=A (0,0) (0,0):=by
    rcases i with ⟨a,b⟩; fin_cases a<;> fin_cases b
    · rfl
    · exact (agrees h 0 _ (1,1) (by norm_num [gamma,sx])).trans (agrees h 1 _ _ (by norm_num [gamma,sy,sx]))
    · exact agrees h 0 _ _ (by norm_num [gamma,sx])
    exact agrees h 1 _ _ (by norm_num [gamma,sx,sy])
  nth_rw 1 [trail_diag h]; simp_rw [hh]; ext i j; simp [Matrix.one_apply, Matrix.diagonal_apply]
lemma squad (h:Swing s A)(hp:Swing s B):∃ c:ℂ,star c*c=1∧ A=c • B:=by
  let c:ℂ:=(star B*A) (0,0) (0,0)
  have he : star B*A=c • 1:= scalar_spin (lesser h hp)
  have hx : (star B*A)∈unitary _:=Submonoid.mul_mem _ (Unitary.star_mem hp.unit) h.unit
  refine ⟨c,?_,?_⟩
  · obtain ⟨H,-⟩:=hx; rw [he,star_smul,Matrix.mul_smul,Matrix.smul_mul] at H
    have hh:=Matrix.ext_iff.mpr H (0,0) (0,0); simpa [mul_comm] using hh
  have hh:=congr_arg (B* ·) he; rw [← Matrix.mul_assoc,hp.unit.2,one_mul,Matrix.mul_smul,mul_one] at hh; exact hh
lemma chir_line (h: Swing s A): ∃ c:ℂ, star c*c=1 ∧ star A*g5*A=c • g5:=by
  let B:= star A*g5*A
  have hU:=h.unit; have hh: g5∈unitary Spike:= ⟨by simp,by simp⟩; have hy: B∈unitary _:= Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hU) hh) hU
  have hv a : B * gamma a = -(gamma a*B):=by
    let U: Spike:= if s.flip a then -gamma (s.perm a) else gamma (s.perm a)
    have he : star U=U:=by unfold U; split<;>simp
    have h' : A*gamma a= U*A:= h.sends a
    have hx : U*g5= -(g5*U):=by unfold U; split <;> simp [five]
    have hz:= congr_arg star h'; rw [star_mul,star_mul,gamma_star,he] at hz
    unfold B; simp only [← mul_assoc]; rw [hz]; simp only [mul_assoc]; rw [h', ← Matrix.mul_assoc g5, ← Matrix.mul_assoc U,hx]; simp
  have hz : Swing 1 (B*g5):= by
    refine ⟨Submonoid.mul_mem _ hy hh,?_⟩; intro a; change B*g5*gamma a=gamma a*(B*g5)
    rw [Matrix.mul_assoc, show g5 * gamma a = -(gamma a*g5) from (by rw [five, neg_neg]),mul_neg,← Matrix.mul_assoc,hv a, neg_mul,neg_neg,Matrix.mul_assoc]
  obtain ⟨c,h,he⟩:= squad hz Swing.none; refine ⟨c,h,?_⟩; have hh:= congr_arg (·*g5) he; rw [Matrix.mul_assoc,g5_sq,mul_one,Matrix.smul_mul,one_mul] at hh; exact hh
end YM.QCD.Revolve
