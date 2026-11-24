import YM.Massive.Target.Covers
import YM.QCD.Revolve.Jolt

/-! # Spinor frame orientation data.

Resolve intrinsic star/transpose signs with the lattice operator conventions
BEFORE choosing lift fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Clifford
open QCD QCD.Lat Lattice Wilson Mink Lorentz Function Matrix QCD.Revolve
open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology Kronecker

private lemma PaTa : sx.transpose=sx:=by ext i j; fin_cases i <;> fin_cases j <;> norm_num [sx]
private lemma PaTb : sy.transpose= -sy:=by ext i j; fin_cases i <;> fin_cases j <;> norm_num [sy]
private lemma PaTc : sz.transpose=sz:=by ext i j; fin_cases i <;> fin_cases j <;> norm_num [sz]
private lemma kron_trans (X Y:Pauli): Matrix.transpose (X ⊗ₖ Y)= (X.transpose) ⊗ₖ (Y.transpose):=rfl
lemma transpose_first : (gamma 0).transpose=gamma 0:=by change Matrix.transpose (sx ⊗ₖ (1:Pauli))=_; rw [kron_trans,PaTa,transpose_one]; rfl
lemma transpose_second : (gamma 1).transpose= -(gamma 1):=by change Matrix.transpose (sy ⊗ₖ sx)=_; rw [kron_trans,PaTb,PaTa,kron_neg]; rfl
lemma transpose_third : (gamma 2).transpose=gamma 2:=by change Matrix.transpose (sy ⊗ₖ sy)=_; rw [kron_trans,PaTb,kron_neg,neg_kron,neg_neg]; rfl
lemma transpose_fourth : (gamma 3).transpose= -(gamma 3):=by change Matrix.transpose (sy ⊗ₖ sz)=_; rw [kron_trans,PaTb,PaTc,kron_neg]; rfl
lemma transpose_five : g5.transpose=g5:=by unfold g5; rw [kron_trans, PaTc, Matrix.transpose_one]

abbrev C : Spike:= chargeMatrix
lemma star_charge : star C = -C:=by unfold C chargeMatrix; rw [star_mul,gamma_star,gamma_star, clifford (show (2:Axis)≠0 by decide)]
lemma charge_sq : C*C = -1:=by rw [C,chargeMatrix, ← mul_assoc, Matrix.mul_assoc (gamma 0),clifford (show (2:Axis)≠0 by decide)]; simp only [mul_neg, ← Matrix.mul_assoc, Lat.gamma_sq, one_mul, neg_mul] -- fix
lemma orthC : C∈unitary Spike:=by constructor; rw [star_charge, neg_mul,charge_sq,neg_neg]; rw [star_charge,mul_neg,charge_sq,neg_neg]
lemma transpose_charge : C.transpose= -C:=by unfold C chargeMatrix; rw [transpose_mul, transpose_first, transpose_third,clifford (show (2:Axis)≠0 by decide)]
lemma real_charge : (starRingEnd ℂ).mapMatrix C = C:=by
    change (star C).transpose=C; rw [star_charge,transpose_neg,transpose_charge,neg_neg]
private lemma comm {a:Axis}(h:a≠0)(ht:a≠2) : gamma a*C=C*gamma a:=by unfold C chargeMatrix; rw [←mul_assoc,clifford h,neg_mul,mul_assoc _ (gamma a),clifford ht,mul_neg,neg_neg,mul_assoc]
lemma transC (a: Axis): gamma a * C= -(C * (gamma a).transpose):=by
    fin_cases a -- lsp
    · change gamma 0 * C= -(C * (gamma 0).transpose); rw [transpose_first]; unfold C chargeMatrix; rw [mul_assoc (gamma 0) (gamma 2), clifford (show (2:Axis)≠0 from by decide)]; simp only [mul_neg, neg_neg]
    · change gamma 1 * C= -(C * (gamma 1).transpose); rw [transpose_second,mul_neg,neg_neg, comm (by decide : (1:Axis)≠0) (by decide)]
    · change gamma 2 * C= -(C*(gamma 2).transpose); rw [transpose_third]; unfold C chargeMatrix; rw [←mul_assoc (gamma 2), clifford (show (2:Axis)≠0 from by decide), neg_mul]
    · change gamma 3 * C= -(C * (gamma 3).transpose); rw [transpose_fourth,mul_neg,neg_neg,comm (by decide : (3:Axis)≠0) (by decide)]
lemma fiveC : g5*C=C*g5:=by unfold C chargeMatrix; rw [mul_assoc (gamma 0) (gamma 2), five 2,mul_neg, ← mul_assoc (gamma 0) g5, five 0, neg_mul, neg_neg, mul_assoc]
end YM.Massive.Clifford
#print axioms YM.Massive.Clifford.transC
