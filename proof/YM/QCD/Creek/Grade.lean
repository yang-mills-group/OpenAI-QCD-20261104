import YM.QCD.Creek.Wake

/-! # Constant coefficient Laplace and CCR
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Function Finset Grass NormedSpace
open scoped Topology BigOperators ContDiff
variable {I : Type*}{A B M: Type*} [Fintype A][Fintype B][Fintype M]
lemma finiteComm (X:Finset I)(F : I→EndA A){Z:EndA A}(hh:∀ i∈X, Commute Z (F i)): Commute Z (∑ i∈X,F i):=by classical exact Commute.sum_right _ _ _ hh
lemma timesComm {V Z:EndA A}(hh: Commute V Z)(a:ℂ) : Commute V (a • Z):=by unfold Commute SemiconjBy; rw [spins,spinner,hh.eq]
-- joint
variable (f:Pairs A↪M)
def pet (i:A):M:=f (Sum.inl i)
def met (i:A):M:=f (Sum.inr i)
def pond (D:Matrix A A ℂ):EndA M:= ∑ i,∑ j,D i j • (v (met f j)*v (pet f i))
def slotP (D : Matrix A A ℂ)(i:A):EndA M:=∑ j,D i j • v (met f j)
def slotM (D : Matrix A A ℂ)(j:A):EndA M:= ∑ i,(-D i j) • v (pet f i)
lemma vpet (D:Matrix A A ℂ)(i:M): Commute (v i) (pond f D):= finiteComm _ _ (hh:=fun _ _=> finiteComm _ _ fun _ _=> timesComm (swapsV ..) _)
lemma cpet (D : Matrix A A ℂ)(i:A): pond f D * l (pet f i)-l (pet f i)*pond f D =slotP f D i:=by
  classical
  unfold pond slotP
  rw [sum_mul,mul_sum,← sum_sub_distrib,sum_eq_single i]
  · rw [sum_mul,mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro j _; rw [spins,spinner]; erw [← smul_sub]; have hp:= whittle (met f j) (pet f i) (pet f i) 1; simp only [met,pet,EmbeddingLike.apply_eq_iff_eq,Sum.inr_ne_inl, if_false, if_true,sub_zero] at hp; exact congr_arg ((D i j) • ·) hp
  · intro j _ hj; rw [sum_mul, mul_sum,← sum_sub_distrib]; apply sum_eq_zero; intro k _; rw [spins,spinner]; erw [← smul_sub]; have hp:= whittle (met f k) (pet f j) (pet f i) 1; have hh : v (met f k)*v (pet f j)*l (pet f i)-l (pet f i)*(v (met f k)*v (pet f j))=0:= hp.trans (by simp [met,pet,hj]); erw [hh,smul_zero]
  simp
lemma mmet (D:Matrix A A ℂ)(i:A): pond f D*l (met f i)-l (met f i)*pond f D=slotM f D i:=by
  classical
  unfold pond slotM
  rw [sum_mul,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl; intro j _; rw [sum_mul,mul_sum,← sum_sub_distrib,sum_eq_single i]
  · rw [spins,spinner]; erw [← smul_sub]; have hp:= whittle (met f i) (pet f j) (met f i) 1; have hh : v (met f i)*v (pet f j)*l (met f i)-l (met f i)*(v (met f i)*v (pet f j))= - v (pet f j):= hp.trans (by simp [met,pet]); erw [hh,smul_neg]; exact (neg_smul (D j i) (v (pet f j))).symm
  · intro k _ h; rw [spins,spinner]; erw [← smul_sub]; have hp:= whittle (met f k) (pet f j) (met f i) 1; have hh : v (met f k)*v (pet f j)*l (met f i)-l (met f i)*(v (met f k)*v (pet f j))=0:= hp.trans (by simp [met,pet,h]); erw [hh,smul_zero]
  simp
lemma skipped (D:Matrix A A ℂ)(i:M)(h:i∉Set.range f): pond f D*l i-l i*pond f D=0:=by
  classical
  unfold pond
  rw [sum_mul, mul_sum, ← sum_sub_distrib]; apply sum_eq_zero; intro k _; rw [sum_mul,mul_sum,← sum_sub_distrib]; apply sum_eq_zero; intro j _
  rw [spins,spinner]; erw [← smul_sub]; have he:= whittle (met f j) (pet f k) i 1; rw [if_neg (show pet f k≠i from fun hp=> h ⟨_,hp⟩),if_neg (show met f j≠i from fun hp=>h ⟨_,hp⟩),sub_zero] at he; erw [he,smul_zero]
lemma roundP {X Y:EndA A}(h:Commute X Y): Commute X (birth Y):=by
  letI : NormedAlgebra ℚ (EndA A):=.restrictScalars ℚ ℂ _
  exact h.exp_right
lemma flops (D:Matrix A A ℂ)(i:M): Commute (v i) (birth (pond f D)):=roundP (vpet ..)
lemma strights (D:Matrix A A ℂ)(i:M)(h:i∉Set.range f): Commute (birth (pond f D)) (l i):= (roundP (Commute.symm (sub_eq_zero.mp (skipped f D i h):Commute (pond f D) (l i)))).symm
lemma earnsP (D:Matrix A A ℂ)(i:A):
  birth (pond f D)*l (pet f i)= l (pet f i)*birth (pond f D)+birth (pond f D)*slotP f D i:=by
    have h : Commute (pond f D) (slotP f D i):= finiteComm _ _ fun j _=> timesComm (vpet ..).symm _
    rw [swerve _ _ _ (cpet ..) h.symm,add_mul,(roundP h.symm).eq]
lemma earnsM (D:Matrix A A ℂ)(i:A):
  birth (pond f D)*l (met f i)= l (met f i)*birth (pond f D)+birth (pond f D)*slotM f D i:=by
    have h : Commute (pond f D) (slotM f D i):= finiteComm _ _ fun j _=> timesComm (vpet ..).symm _
    rw [swerve _ _ _ (mmet ..) h.symm,add_mul,(roundP h.symm).eq]
end YM.QCD.Creek
