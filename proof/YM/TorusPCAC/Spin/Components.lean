import YM.TorusPCAC.Spin.Gamma
import YM.QCD.Revolve.Jolt

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Components under signed-coordinate operations

The useful converse rank tool: send all axis reflections with same sign
character, then the simultaneous Spin-matrix eigenspaces have only one
dimension per **off-diagonal pair of flavors** and fixed pair of leg slots
(not counting derivatives). No assumption of Lie algebra generation on the
physical theory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Spin
open QCD QCD.Lat Lattice Finset NormedSpace Revolve
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius Kronecker

lemma spin_product (i j : Axis) : mirrorMatrix i * mirrorMatrix j=gamma i*gamma j:=by
  unfold mirrorMatrix; rw [smul_mul_smul_comm,neg_mul_neg,Complex.I_mul_I]; rw [mul_assoc,← mul_assoc g5, show g5*gamma j = -(gamma j*g5) from (by rw [five,neg_neg]),neg_mul,mul_assoc (gamma j),g5_sq,mul_one]; simp
lemma fifth_cliff : mirrorMatrix 0 * mirrorMatrix 1 * (mirrorMatrix 2*mirrorMatrix 3)= -g5:=by
  -- Lee symmetrical; rederive here for this Pin convention
  have he : sx*sy=Complex.I • sz:=by ext i j; fin_cases i <;> fin_cases j <;> simp [sx,sy,sz,Matrix.mul_apply,Fin.sum_univ_succ]
  rw [spin_product, spin_product]; change (sx⊗ₖ(1:Pauli))*(sy⊗ₖsx)*((sy⊗ₖsy)*(sy⊗ₖsz))=-g5
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,he,yy,one_mul,mul_one,← mul_assoc sx,he,Matrix.smul_mul,zz, Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,Complex.I_mul_I,neg_one_smul]; rfl

namespace MatrixColor
variable (A B : Spike)
lemma chained (h : ∀ i, Commute A (mirrorMatrix i)) : A=A (0,0) (0,0) • 1 :=by
  have hp:= ( (h 0).mul_right (h 1)).mul_right ((h 2).mul_right (h 3)); rw [fifth_cliff] at hp
  apply Revolve.scalar_spin; intro i; have hv:Commute A g5:=by simpa only [neg_neg] using hp.neg_right
  have he : Complex.I • (mirrorMatrix i * g5)=gamma i:=by rw [mirrorMatrix, Matrix.smul_mul,mul_assoc,g5_sq,mul_one,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul]

  rw [← he]; exact ((h i).mul_right hv).smul_right Complex.I

def turn (x : Pin) : Spike→ₐ[ℂ] Spike where
  toFun A := x.val.2.val * A * x.val.2⁻¹.val
  map_one' := by rw [mul_one]; exact x.val.2.val_inv
  map_mul' A B:= by simp only [mul_assoc]; rw [← mul_assoc (x.val.2⁻¹.val) (x.val.2.val), show x.val.2⁻¹.val * x.val.2.val=1 from x.val.2.inv_val,one_mul]
  map_zero' :=by simp
  map_add' _ _:= by simp [add_mul,mul_add]
  commutes' r:= by rw [← (Algebra.commutes r x.val.2.val),mul_assoc,show x.val.2.val*x.val.2⁻¹.val=1 from x.val.2.val_inv,mul_one]
lemma pivot (x : Pin) (i : Axis) : turn x (gamma i)=direction x.val.1.val i:=by
  change x.val.2.val * _ * _ = _; rw [(Lift.certified _).sends,mul_assoc,show x.val.2.val*x.val.2⁻¹.val=1 from x.val.2.val_inv,mul_one]
lemma turn_one (i : Axis) : turn (mirror i) A=mirrorMatrix i*A*mirrorMatrix i:=rfl
lemma turn_fifth (x : Pin) : turn x g5=(x.val.1.val.det : ℂ) • g5:=by
  change x.val.2.val * _ * _ = _; rw [(Lift.certified _).fifth,mul_assoc, show x.val.2.val*x.val.2⁻¹.val=1 from x.val.2.val_inv,mul_one]; exact RCLike.real_smul_eq_coe_smul (K:=ℂ) ..
lemma twice (i : Axis) : Function.Involutive (turn (mirror i)):=by intro x; rw [turn_one,turn_one]; simp only [mul_assoc]; rw [mirrorMatrix_square, mul_one,← mul_assoc (mirrorMatrix i), mirrorMatrix_square,one_mul]
lemma parallel (i j : Axis) : Function.Commute (turn (mirror i)) (turn (mirror j)):=by
  by_cases hi : i=j; · subst j; exact fun _=> rfl
  intro A; simp_rw [turn_one];
  have he (X Y Z:Spike): X*(Y*Z*Y)*X= X*Y*Z*(Y*X):=by simp [mul_assoc]
  rw [he,he,spin_product,spin_product]; rw [clifford hi]; simp
lemma dimension {f : Axis→ℂ} (h : ∀ i, f i * f i=1) (hp : ∀ i, turn (mirror i) A=f i • A)
    (hc : IsUnit B) (hm : ∀ i, turn (mirror i) B=f i • B): ∃ v : ℂ, A=v • B :=by
  let T:= Ring.inverse B
  have ht:T*B=1:= Ring.inverse_mul_cancel _ hc
  have hu:B*T=1:= Ring.mul_inverse_cancel _ hc
  have hv i : turn (mirror i) T=f i • T:=by
    apply (hc.map (turn (mirror i))).mul_right_cancel
    rw [← map_mul,ht,map_one,hm, smul_mul_smul_comm,h,one_smul,ht]
  have he:∀ i, Commute (A*T) (mirrorMatrix i):=by
    intro i; have hp:= show turn (mirror i) (A*T)=A*T by rw [map_mul,hp,hv, smul_mul_smul_comm, h,one_smul];
    rw [turn_one] at hp; change (A*T)*_= _*(A*T); nth_rw 1 [← hp]; rw [mul_assoc _ (mirrorMatrix i) (mirrorMatrix i), mirrorMatrix_square, mul_one]
  let v:ℂ:=(A*T) (0,0) (0,0); refine ⟨v,?_⟩; have hq:=(congr_arg (· * B) (chained (A*T) he)); rw [mul_assoc,ht,mul_one,Matrix.smul_mul, one_mul] at hq; exact hq
end MatrixColor
end YM.TorusPCAC.Spin

#print axioms YM.TorusPCAC.Spin.MatrixColor.dimension
