import YM.MassiveTwoEstimates.SpinFibres
import YM.Ground.Lean

/-! Clifford identities for the actual matrices and Euclidean inner product
in the target spin-cover presentation. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinClifford
open Massive QCD.Lat Matrix Finset
open scoped BigOperators InnerProductSpace Kronecker

theorem slashSub (x y : E4) : slash (x-y) = slash x-slash y := by
  simp [slash,sub_smul,Finset.sum_sub_distrib]

theorem slashSmul (t : ℝ) (x : E4) : slash (t • x) = (t:ℂ) • slash x := by
  unfold slash
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((t * x i : ℝ) : ℂ) • gamma i = (t:ℂ) • ((x i : ℂ) • gamma i)
  rw [Complex.ofReal_mul,smul_smul]

private theorem gammaAnti (i j : Axis) : gamma i*gamma j+gamma j*gamma i =
    if i=j then (2:ℂ) • (1:Spike) else 0 := by
  split
  · subst j
    simp [two_smul]
  · rename_i h
    rw [clifford h,neg_add_cancel]

private lemma oneAnti (i : Axis) (x : E4) : gamma i * slash x + slash x * gamma i =
    (2 * (x i : ℂ)) • (1:Spike) := by
  classical
  unfold slash
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib,Matrix.mul_smul,
    Matrix.smul_mul,←smul_add,gammaAnti]
  rw [Finset.sum_eq_single i]
  · simp [smul_smul,mul_comm]
  · intro j _ away
    simp [away.symm]
  · simp

/-- Real Euclidean polarization on the concrete spin representation. -/
theorem polarized (u x : E4) : slash u * slash x + slash x * slash u =
    ((2 * inner ℝ u x : ℝ) : ℂ) • (1:Spike) := by
  classical
  calc
    _ = ∑ i, (u i : ℂ) • (gamma i*slash x + slash x*gamma i) := by
      conv_lhs => rw [show slash u = ∑ i, (u i : ℂ) • gamma i from rfl]
      simp only [Finset.sum_mul,Finset.mul_sum,Matrix.smul_mul,Matrix.mul_smul,
        smul_add,Finset.sum_add_distrib]
    _ = _ := by
      simp only [oneAnti,smul_smul,← Finset.sum_smul]
      congr 1
      rw [PiLp.inner_apply]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [RCLike.inner_apply]
      ring

theorem square (u : E4) : slash u * slash u = ((‖u‖^2 : ℝ) : ℂ) • (1:Spike) := by
  have h := polarized u u
  rw [real_inner_self_eq_norm_sq,Complex.ofReal_mul,Complex.ofReal_ofNat,
    ← smul_smul,←two_smul ℂ] at h
  exact (smul_right_injective _ (by norm_num : (2:ℂ) ≠ 0)) h

theorem transposeGamma (a : Axis) :
    (gamma a).transpose = if a = 0 ∨ a = 2 then gamma a else -gamma a := by
  have axis : a=0 ∨ a=1 ∨ a=2 ∨ a=3 := by fin_cases a <;> decide
  rcases axis with rfl | rfl | rfl | rfl
  case' inl =>
    rw [if_pos (Or.inl rfl)]
    change (sx ⊗ₖ (1:Pauli)).transpose = sx ⊗ₖ (1:Pauli)
  case' inr.inl =>
    rw [if_neg (by decide : ¬ ((1:Axis)=0 ∨ (1:Axis)=2))]
    change (sy ⊗ₖ sx).transpose = -(sy ⊗ₖ sx)
  case' inr.inr.inl =>
    rw [if_pos (Or.inr rfl)]
    change (sy ⊗ₖ sy).transpose = sy ⊗ₖ sy
  case' inr.inr.inr =>
    rw [if_neg (by decide : ¬ ((3:Axis)=0 ∨ (3:Axis)=2))]
    change (sy ⊗ₖ sz).transpose = -(sy ⊗ₖ sz)
  all_goals
    ext ⟨i,k⟩ ⟨j,l⟩
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      norm_num [sx,sy,sz,Matrix.one_apply]

private lemma commuteSign (a b : Axis) : gamma a*gamma b =
    (if a=b then (1:ℂ) else -1) • (gamma b*gamma a) := by
  by_cases h : a=b
  · simp [h]
  · simpa [h] using clifford h

theorem chargeGamma (a : Axis) : gamma a * chargeMatrix = -(chargeMatrix*(gamma a).transpose) := by
  have slide : gamma a * chargeMatrix =
      ((if a=0 then (1:ℂ) else -1)*(if a=2 then (1:ℂ) else -1)) • (chargeMatrix*gamma a) := by
    unfold chargeMatrix
    calc
      _ = (gamma a * gamma 0) * gamma 2 := (Matrix.mul_assoc ..).symm
      _ = (if a=0 then (1:ℂ) else -1) • (gamma 0 * (gamma a*gamma 2)) := by
        rw [commuteSign a 0,Matrix.smul_mul,Matrix.mul_assoc]
      _ = _ := by rw [commuteSign a 2,Matrix.mul_smul,smul_smul,Matrix.mul_assoc]
  rw [slide,transposeGamma]
  by_cases h0 : a=0 <;> by_cases h2 : a=2 <;>
    simp [h0,h2] at *

theorem chargeSlash (u : E4) : slash u * chargeMatrix = -(chargeMatrix*(slash u).transpose) := by
  simp only [slash,Finset.sum_mul,Matrix.smul_mul,chargeGamma,transpose_sum,
    transpose_smul,Finset.mul_sum,Matrix.mul_smul,smul_neg,Finset.sum_neg_distrib]

theorem fiveSlash (u : E4) : slash u * g5 = -(g5 * slash u) := by
  simp only [slash,Finset.sum_mul,Matrix.smul_mul,five,smul_neg,Finset.sum_neg_distrib,
    Finset.mul_sum,Matrix.mul_smul]

end YM.MassiveTwoEstimates.SpinClifford
#print axioms YM.MassiveTwoEstimates.SpinClifford.polarized
#print axioms YM.MassiveTwoEstimates.SpinClifford.square
#print axioms YM.MassiveTwoEstimates.SpinClifford.chargeSlash
