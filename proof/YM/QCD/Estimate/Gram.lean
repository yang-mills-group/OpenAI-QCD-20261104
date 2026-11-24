import YM.QCD.Estimate.Accretive
import YM.QCD.Grass.Wick
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Grassmann determinants without factorial loss

At coercive blocks or with any spectral bound. Works for subminors and smeared probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cost
open Finset InnerProductSpace Function Grass
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def ticket (x y : Fin k→ E) : Mx (Fin k) := Matrix.of fun i j => inner ℂ (x i) (y j)
lemma over (x y : Fin k→ E) : ticket x y = star (ticket y x) := by ext i j; exact (inner_conj_symm _ _).symm

lemma shrink (x : Fin k → E) (i : Fin k) : ‖gramSchmidt ℂ x i‖ ≤ ‖x i‖ := by
  let z := gramSchmidt ℂ x
  have h := gramSchmidt_def'' ℂ x i
  have he : inner ℂ (z i) (x i)=inner ℂ (z i) (z i) := by
    conv_lhs => rw [h]
    rw [inner_add_right, inner_sum, sum_eq_zero]; exact add_zero _
    intro b hb; rw [inner_smul_right, gramSchmidt_orthogonal ℂ _ (mem_Iio.mp hb).ne', mul_zero] -- fix
  by_cases hp : z i=0
  · change ‖z i‖ ≤ _; rw [hp,norm_zero]; exact norm_nonneg _
  have hu := norm_inner_le_norm (𝕜:=ℂ) (z i) (x i)
  have hh := inner_self_eq_norm_sq (𝕜:=ℂ) (z i); rw [he] at hu
  have hu := (RCLike.re_le_norm (inner ℂ (z i) (z i))).trans hu
  rw [hh,sq] at hu
  exact le_of_mul_le_mul_left hu (norm_pos_iff.mpr hp)

lemma clipping (x y : Fin k → E) : (ticket x y).det=(ticket (gramSchmidt ℂ x) y).det := by
  let z := gramSchmidt ℂ x
  let a (i b : Fin k) := star ((inner ℂ (z b) (x i))/(‖z b‖:ℂ)^2)
  let B := Matrix.of (fun i b => if b < i then a i b else 0)
  have hh : ticket x y=(1+B)*ticket z y := by
    ext i j
    rw [add_mul,one_mul,Matrix.add_apply]; change inner ℂ (x i) (y j)=inner ℂ (z i) (y j)+_
    conv_lhs => rw [gramSchmidt_def'' ℂ x i]
    rw [inner_add_left,sum_inner]; congr 1
    simp_rw [inner_smul_left]; rw [Matrix.mul_apply]
    change ∑ b∈Iio i, a i b * _ = ∑ b, B i b * _
    calc
      _ = ∑ b ∈ Iio i, B i b*ticket z y b j := sum_congr rfl fun b hb => by simp only [B,Matrix.of_apply,mem_Iio.mp hb,if_true]; rfl
      _ = _ := sum_subset (subset_univ _) (fun j _ hj => by simp only [B,Matrix.of_apply, if_neg (mt mem_Iio.mpr hj),zero_mul])
  have hb : (1+B).det=1 := by
    rw [Matrix.det_of_lowerTriangular]; simp [B]
    intro i j hij; change i<j at hij; simp [B,hij.ne,not_lt.mpr hij.le]
  rw [hh, Matrix.det_mul,hb,one_mul]

lemma distillation (x y : Fin k→ E) : (ticket x y).det=(ticket (gramSchmidt ℂ x) (gramSchmidt ℂ y)).det := by
  rw [clipping x y,over (gramSchmidt ℂ x) y,over (gramSchmidt ℂ x) (gramSchmidt ℂ y)] -- likely wrong arity
  simp only [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; rw [clipping y]

lemma from_orth (x y : Fin k → E) (hx : Orthonormal ℂ x) (hy : Orthonormal ℂ y) : ‖(ticket x y).det‖ ≤ 1 := by
  have h (f : Vec (Fin k)) : ‖op (ticket x y) f‖ ≤ 1*‖f‖ := by
    let U := ∑ i, f i • y i
    have hn : ‖U‖^2=‖f‖^2 := by
      have hu : inner ℂ U U = inner ℂ f f := by
        dsimp only [U]; rw [hy.inner_sum,PiLp.inner_apply]
        refine sum_congr rfl fun i _ => ?_; rw [RCLike.inner_apply,mul_comm]
      rw [← inner_self_eq_norm_sq (𝕜:=ℂ),← inner_self_eq_norm_sq (𝕜:=ℂ), hu]
    have ht (i) : (op (ticket x y) f) i=inner ℂ (x i) U := by
      dsimp only [U]; rw [inner_sum]; change ∑ j, inner ℂ (x i) (y j) * f j = _
      exact sum_congr rfl fun j _ => by rw [inner_smul_right,mul_comm]
    rw [one_mul, ← sq_le_sq₀ (by positivity) (by positivity), ← hn, EuclideanSpace.norm_sq_eq]
    simp_rw [ht]; exact hx.sum_inner_products_le U
  simpa using max_det _ h zero_le_one

lemma normal (x : Fin k → E) (hx : ∀ i, gramSchmidt ℂ x i≠0) : Orthonormal ℂ (gramSchmidtNormed ℂ x) := by
  refine ⟨fun i => gramSchmidtNormed_unit_length' (by simp [gramSchmidtNormed,hx]),?_⟩
  intro i j h
  unfold gramSchmidtNormed; rw [inner_smul_left,inner_smul_right, gramSchmidt_orthogonal ℂ x h,mul_zero,mul_zero]

lemma adjust (x : Fin k → E) (i : Fin k) : gramSchmidt ℂ x i = (‖gramSchmidt ℂ x i‖:ℂ) • gramSchmidtNormed ℂ x i := by
  by_cases h : gramSchmidt ℂ x i=0
  · simp [h]
  change gramSchmidt ℂ x i = (‖gramSchmidt ℂ x i‖:ℂ) • ((‖gramSchmidt ℂ x i‖:ℂ)⁻¹ • _)
  rw [smul_smul, mul_inv_cancel₀ (by simpa),one_smul]

def prism (x : Fin k → E) := Matrix.diagonal fun i => (‖gramSchmidt ℂ x i‖:ℂ)
lemma dial (x y : Fin k → E) : ticket (gramSchmidt ℂ x) (gramSchmidt ℂ y)=
    prism x*ticket (gramSchmidtNormed ℂ x) (gramSchmidtNormed ℂ y)*prism y := by
  ext i j
  conv_lhs => rw [ticket,Matrix.of_apply, adjust x i, adjust y j]
  rw [inner_smul_left,inner_smul_right]; simp [ticket,prism]; ring

lemma paying (x : Fin k → E) : ‖(prism x).det‖ ≤ ∏ i, ‖x i‖ := by
  simp only [prism,Matrix.det_diagonal,norm_prod, Complex.norm_real,Real.norm_eq_abs,abs_norm]
  exact prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => shrink x i)

lemma punch (x y : Fin k → E) : ‖(ticket x y).det‖ ≤ (∏ i, ‖x i‖) * ∏ i, ‖y i‖ := by
  rw [distillation]
  by_cases hx : ∀ i, gramSchmidt ℂ x i ≠ 0
  · by_cases hy : ∀ i, gramSchmidt ℂ y i≠0
    · rw [dial,Matrix.det_mul,Matrix.det_mul,norm_mul,norm_mul]
      exact mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) (from_orth _ _ (normal x hx) (normal y hy))).trans (paying x)) (paying y) (by positivity) (by positivity)
    push Not at hy; obtain ⟨i,hi⟩ := hy
    rw [Matrix.det_eq_zero_of_column_eq_zero i (by simp [ticket,hi]),norm_zero]; positivity
  push Not at hx; obtain ⟨i,hi⟩ := hx
  rw [Matrix.det_eq_zero_of_row_eq_zero i (by simp [ticket,hi]),norm_zero]; positivity

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma conforms (H : Mx A) (Q P : Matrix (Fin k) A ℂ) :
    lineup H Q P=ticket (fun i => WithLp.toLp 2 (star (Q i)) : Fin k → Vec A) (fun i => op H (WithLp.toLp 2 (P i))) := by
  ext i j; rw [ticket, Matrix.of_apply,PiLp.inner_apply]
  rw [lineup, Matrix.mul_assoc,Matrix.mul_apply]
  refine sum_congr rfl fun a _ => ?_
  rw [RCLike.inner_apply]; change Q i a * _ = _ * star (star (Q i a)); rw [star_star,mul_comm]; rfl
lemma payout (H : Mx A) (Q P : Matrix (Fin k) A ℂ) :
    ‖(lineup H Q P).det‖ ≤ (∏ i, ‖(WithLp.toLp 2 (Q i) : Vec A)‖)*∏ i, (‖H‖*‖(WithLp.toLp 2 (P i):Vec A)‖) := by
  rw [conforms]
  have he (i) : ‖(WithLp.toLp 2 (star (Q i)):Vec A)‖=‖(WithLp.toLp 2 (Q i):Vec A)‖ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity),EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]; simp
  refine (punch _ _).trans ?_; simp_rw [he];
  refine mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_) (by positivity)
  rw [Matrix.cstar_norm_def H]; exact (op H).le_opNorm _

/-- gram price by spectral inverse, finite lattice. -/
lemma price_wick (D : Mx A) (h : IsUnit D.det) (Q P : Matrix (Fin k) A ℂ) :
    ‖seen D (bundle Q*twigs P)‖ ≤ (∏ i, ‖(WithLp.toLp 2 (Q i):Vec A)‖)*∏ i,(‖D⁻¹‖*‖(WithLp.toLp 2 (P i):Vec A)‖) := by rw [wick D h]; exact payout ..

end YM.QCD.Cost
