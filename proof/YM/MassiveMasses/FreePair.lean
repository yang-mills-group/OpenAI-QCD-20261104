import YM.Massive.Target.Wick
import YM.QCD.Free.Symbol
import YM.Maxwell.PotentialKernel

/-! Explicit four-spin, three-colour comparison for a separated ordinary
pseudoscalar pair.  Its two propagators come from the fixed comparison
Dirac kernel in the massive theory's target. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveMasses.FreePair
open Lattice QCD QCD.Lat Maxwell
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

def factor (x : E4) : ℝ := 2 * Maxwell.normal * ((‖x‖^2)⁻¹)^2
def prop (x : E4) : Bundle := (factor x : ℂ) • QCD.Free.slash (fun a => x a)

/-- This is the target's spinor kernel extended diagonally over the three colors. -/
theorem prop_entry (x : E4) (hx : x ≠ 0) (s t : Pinor) (c d : Hue) :
    prop x (s,c) (t,d) = if c = d then Massive.UV.Free.dirac s t x else 0 := by
  by_cases hc : c = d
  · subst d
    simp only [prop, QCD.Free.slash, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, wave,
      Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, if_true, eq_self,
      Massive.UV.Free.dirac, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have h := Maxwell.first_Green hx a
    change YM.Analysis.D (basis a) Maxwell.Green x = _ at h
    rw [h]
    unfold factor
    push_cast
    ring
  · simp [prop,QCD.Free.slash,Matrix.sum_apply,wave,Matrix.kroneckerMap_apply,Matrix.one_apply_ne hc,hc]

theorem prop_neg (x : E4) : prop (-x) = -prop x := by
  simp only [prop,factor,norm_neg,QCD.Free.slash,PiLp.neg_apply,Complex.ofReal_neg,
    neg_smul,Finset.sum_neg_distrib,smul_neg]

theorem gammaFlip (x : E4) : wave g5 * prop x * wave g5 = -prop x := by
  have block (a : Axis) : wave g5 * wave (gamma a) * wave g5 = -wave (gamma a) := by
    rw [wave_mul,wave_mul,mul_assoc,five,mul_neg,← mul_assoc,g5_sq,one_mul]
    ext ⟨s,c⟩ ⟨t,d⟩
    simp [wave,Matrix.kroneckerMap_apply]
  simp only [prop,QCD.Free.slash,Matrix.mul_smul,Matrix.smul_mul,Finset.mul_sum,
    Finset.sum_mul, block, smul_neg, Finset.sum_neg_distrib]

def wickTrace (x : E4) : ℂ := -Matrix.trace (wave g5 * prop x * wave g5 * prop (-x))

theorem wickTrace_value (x : E4) (hx : x ≠ 0) :
    wickTrace x = -((3 / (Real.pi^4 * ‖x‖^6) : ℝ) : ℂ) := by
  rw [wickTrace,prop_neg,gammaFlip,neg_mul_neg]
  have hsq : (QCD.Free.lensq (fun a => x a)) = ‖x‖^2 := by
    exact (EuclideanSpace.real_norm_sq_eq x).symm
  have hc : Fintype.card Fiber = 12 := by decide
  simp only [prop,Matrix.smul_mul,Matrix.mul_smul,QCD.Free.slash_sq,hsq,Matrix.trace_smul,
    smul_eq_mul,Matrix.trace_one,hc]
  have hπ := Real.pi_ne_zero
  have ht : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  unfold factor Maxwell.normal
  push_cast
  field_simp
  ring

theorem uniform_off_diagonal {x y : E4} {R : ℝ} (hxy : x ≠ y) (hR : ‖x-y‖ ≤ R) :
    0 < 3 / (Real.pi^4 * R^6) ∧
    3 / (Real.pi^4 * R^6) ≤ -(wickTrace (x-y)).re := by
  have hp := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hR' := hp.trans_le hR
  rw [wickTrace_value _ (sub_ne_zero.mpr hxy)]
  simp only [Complex.neg_re,Complex.ofReal_re,neg_neg]
  constructor
  · positivity
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hR 6) (by positivity))

end YM.MassiveMasses.FreePair
#print axioms YM.MassiveMasses.FreePair.prop_entry
#print axioms YM.MassiveMasses.FreePair.uniform_off_diagonal
