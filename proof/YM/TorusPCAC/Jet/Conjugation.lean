import YM.TorusPCAC.Jet.Triple

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Charge and five-parity at physical readouts -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet
open QCD QCD.Lat Finset Function MeasureTheory TensorProduct Spin
open scoped Matrix Topology BigOperators Kronecker TensorProduct Matrix.Norms.Frobenius

namespace Selector
lemma inverse_C : Cmat⁻¹=gamma 2*gamma 0:= by
  apply Matrix.inv_eq_left_inv
  unfold Cmat; rw [← mul_assoc _ (gamma 0) _, Matrix.mul_assoc (gamma 2), gamma_sq, mul_one,gamma_sq]
lemma pays_C : Cmat⁻¹ * Cmat=1:=by rw [inverse_C,Cmat, ← mul_assoc _ (gamma 0) _,Matrix.mul_assoc (gamma 2),gamma_sq,mul_one,gamma_sq]
lemma pays_C' : Cmat*Cmat⁻¹=1:=mul_eq_one_comm.mp pays_C
lemma g5_trans : g5ᵀ=g5:=by ext ⟨i,j⟩ ⟨k,l⟩; by_cases h : i=k <;> by_cases he:j=l <;> simp [g5,sz,h,he,Ne.symm]; all_goals fin_cases i <;> fin_cases k <;> simp_all
lemma turns_C_G5 : (Cmat⁻¹*g5*Cmat)ᵀ=g5:=by
  have he:g5*Cmat=Cmat*g5:=by unfold Cmat; rw [← mul_assoc, show g5*gamma 0= -(gamma 0*g5) from (by rw [Lat.five,neg_neg]),neg_mul]; simp only [mul_assoc]; rw [Lat.five 2]; simp
  rw [mul_assoc,he,← mul_assoc, pays_C,one_mul,g5_trans]
lemma moves_C (p : Axis) : (Cmat⁻¹*gamma p * Cmat)ᵀ= -gamma p:=by
  have hg : (sx)ᵀ=sx:=by ext i j; fin_cases i<;> fin_cases j<;> simp [sx]
  have hz : (sz)ᵀ=sz:=by ext i j; fin_cases i<;> fin_cases j<;> simp [sz]
  have hh : (sy)ᵀ= -sy:=by ext i j; fin_cases i<;> fin_cases j<;>simp [sy]
  have transit (x y:Pauli): (x⊗ₖy)ᵀ=xᵀ⊗ₖyᵀ:=rfl
  suffices he : gamma p * Cmat= -(Cmat*(gamma p)ᵀ) by
    rw [mul_assoc,he,mul_neg,← mul_assoc, pays_C, one_mul,Matrix.transpose_neg,Matrix.transpose_transpose]
  by_cases hp:p=0
  · subst p; unfold Cmat; rw [show (gamma 0)ᵀ=gamma 0 from (by change (sx ⊗ₖ (1:Pauli))ᵀ=_; rw [transit,hg,Matrix.transpose_one]; rfl),mul_assoc (gamma 0),clifford (by decide: (2:Axis)≠0),mul_neg,neg_neg]
  by_cases hk:p=2
  · subst p; unfold Cmat; rw [show (gamma 2)ᵀ=gamma 2 from (by change (sy ⊗ₖ sy)ᵀ=_; rw [transit,hh]; simp only [Lat.kron_neg, Lat.neg_kron,neg_neg]; rfl),← mul_assoc, clifford (by decide : (2:Axis)≠0),neg_mul];
  have he : p=1 ∨ p=3:=by fin_cases p <;> simp_all
  have he' : (gamma p)ᵀ= -gamma p:=by
    rcases he with he|he; · subst p; change (sy ⊗ₖ sx)ᵀ= - _; rw [transit,hg,hh,kron_neg]; rfl
    subst p; change (sy ⊗ₖ sz)ᵀ= - _; rw [transit,hh,hz, kron_neg]; rfl
  rw [he',mul_neg,neg_neg]; unfold Cmat; rw [← mul_assoc, clifford hp, neg_mul,mul_assoc,mul_assoc, clifford hk,mul_neg,neg_neg]

abbrev changeSign (s : Bool) : ℂ := if s then 1 else -1

def Cscore (X : Spike) := (Cmat⁻¹ * X * Cmat)ᵀ
def score5 (X : Spike) := g5 * Xᴴ * g5
lemma theme_C (s): Cscore (theme s)=theme s:=by cases s; exact show (Cmat⁻¹ *1* Cmat)ᵀ= _ from (by rw [mul_one,pays_C,Matrix.transpose_one]; rfl); exact turns_C_G5
lemma theme5 (s): score5 (theme s)=theme s:=by cases s; change g5*(1:Spike)ᴴ*_=_; simp [theme]; change g5*star g5*g5=_; rw [g5_star,g5_sq,one_mul]; rfl -- check
lemma Cchar (s)(p : Axis) : Cscore (path s p)=changeSign s • path s p:=by
  have he : Cscore (path s p)=Cscore (theme s)*Cscore (gamma p):=by
    unfold Cscore path; rw [← Matrix.transpose_mul]; congr 1
    simp only [mul_assoc]; rw [← mul_assoc Cmat Cmat⁻¹,pays_C', one_mul]
  rw [he,theme_C, show Cscore (gamma p)=_ from moves_C p]; cases s <;> simp [changeSign,path,theme,Lat.five]
lemma vchar (s)(p : Axis) : score5 (path s p)=changeSign s • path s p:=by
  unfold score5 path; rw [← Matrix.star_eq_conjTranspose,star_mul,gamma_star]; cases s <;> simp only [theme,Bool.false_eq_true,↓reduceIte,g5_star,star_one,one_smul,one_mul,neg_smul,mul_one, changeSign]
  · rw [show g5*gamma p=_ from (by rw [Lat.five,neg_neg] : g5*gamma p=-(gamma p*g5)),neg_mul,mul_assoc,g5_sq,mul_one]
  rw [← mul_assoc _ g5 _,g5_sq,one_mul]
end Selector
end YM.TorusPCAC.Jet

#print axioms YM.TorusPCAC.Jet.Selector.vchar
#print axioms YM.TorusPCAC.Jet.Selector.turns_C_G5
