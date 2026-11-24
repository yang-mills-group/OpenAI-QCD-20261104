import YM.Mako.Seed
import YM.MassiveTwoEstimates.SpinGeometry
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Analysis Lattice
open Massive MassiveTwoEstimates MassiveTwoEstimates.SpinGeometry
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
open NormedSpace
-- cf. YM.Work.A10
def conjSkew (A : Ortho) (g : Ortho.Skew) : Ortho.Skew :=
  ⟨A.val * g.val * star A.val, by
    change star _ = -_
    have h : star g.val = -g.val := g.property
    simp only [star_mul, star_star, h, neg_mul, ← mul_assoc, mul_neg]⟩

lemma oneParameter_conj (A : Ortho) (g : Ortho.Skew) (t : ℝ) :
    Ortho.oneParameter (conjSkew A g) t = A * Ortho.oneParameter g t * A⁻¹ := by
  apply Subtype.ext
  change exp (t • (A.val * g.val * star A.val)) = A.val * exp (t • g.val) * star A.val
  haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  let w : M4ˣ := ⟨A.val, star A.val, A.property.2, A.property.1⟩
  rw [show t • (A.val * g.val * star A.val) = A.val * (t • g.val) * star A.val by simp]
  exact exp_units_conj w _

lemma oneParameter_zero (g : Ortho.Skew) : Ortho.oneParameter g 0 = 1 := by
  apply Subtype.ext
  change exp ((0 : ℝ) • g.val) = (1 : M4)
  simp

/-- The variation of Ad along `exp(t u)`, as a derivative in the skew subspace. -/
lemma conj_deriv (u v : Ortho.Skew) :
    HasDerivAt (fun t => conjSkew (Ortho.oneParameter u t) v) (Org.bracket u v) 0 := by
  let a := fun t => (Ortho.oneParameter u t).val
  have he : HasDerivAt a u.val 0 := by
    simpa [a, Ortho.oneParameter] using! hasDerivAt_exp_smul_const u.val (0 : ℝ)
  have h : HasDerivAt (fun t => (conjSkew (Ortho.oneParameter u t) v).val)
      (Org.bracket u v).val 0 := by
    have hz := (he.mul_const v.val).mul he.star
    have ha : a 0 = 1 := by simp [a, Ortho.oneParameter]
    change HasDerivAt (fun t => a t * v.val * star (a t))
      (u.val * v.val - v.val * u.val) 0
    have hu : star u.val = -u.val := u.property
    simpa only [ha, one_mul, star_one, hu, mul_one, mul_neg, sub_eq_add_neg] using! hz
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_subtype_rng.mpr
  exact h.tendsto_slope_zero

lemma conjug (g:Ortho.Skew)(Δ:ℝ→ EuPin)(h:EuPin.Path g Δ)(ρ:EuPin): EuPin.Path (conjSkew ρ.coord g) (fun t=>ρ*Δ t*ρ⁻¹):=by
    refine ⟨?_, continuous_const.mul h.2.1 |>.mul continuous_const,?_⟩; · simp [h.1]
    intro t; change euca (ρ*Δ t*ρ⁻¹) = _; rw[map_mul,map_mul,map_inv,oneParameter_conj,show euca (Δ t)=Ortho.oneParameter g t from h.2.2 t]; rfl
end YM.Mako
#print axioms YM.Mako.conjug
#print axioms YM.Mako.conj_deriv
