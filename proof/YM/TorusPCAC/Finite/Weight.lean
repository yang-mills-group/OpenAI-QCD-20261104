import YM.TorusPCAC.Spec.Regulator

/-!
# Joint finite-mass regulator vs. `Cut`

Decompose exactly as a common regulator times a gauge-invariant onsite
Grassmann polynomial. No inverse matrix on the fermions and no pairing of
flavors. This handles *negative, different* bare masses; the RG argument in
`work/bend` uses such a possibility. Claim reality (not positivity yet).
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC
open Wilson Lattice MeasureTheory QCD QCD.Lat
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {N : ℕ}

namespace Torus

variable (B : Torus n N)

/-- Zero bare-mass `Lat.Cut`, before changing individual bare masses. -/
def starter : Cut n N := ⟨B.beta,B.seam,0⟩

/-- Reverse dictionary for the supplied theorem about common bare mass. -/
def uniform (C : Cut n N) : Torus n N := ⟨C.t,C.β,fun _ => C.m⟩

@[simp] theorem uniform_beta (C : Cut n N) : (uniform C).beta = C.β := rfl
@[simp] theorem uniform_seam (C : Cut n N) : (uniform C).seam = C.t := rfl
@[simp] theorem uniform_mass (C : Cut n N) (i : Flavor N) : (uniform C).mass i = C.m := rfl
@[simp] theorem uniform_fermion (C : Cut n N) (U) : (uniform C).fermion U = C.ferm U := rfl

lemma block_read (U : Grid n) (i j : Modes n N) : B.fermion U i j =
    if i.2=j.2 then bareD B.seam U (B.mass i.2) i.1 j.1 else 0 :=
  Matrix.blockDiagonal_apply .. -- test

/-- Magnitudes still possibly signful; this is the *full* sea result. -/
theorem trace_det (U) : (B.fermion U).det = ∏ i : Flavor N, (bareD B.seam U (B.mass i)).det :=
  Matrix.det_blockDiagonal _

@[fun_prop] theorem continuous_fermion : Continuous B.fermion := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp_rw [block_read]
  split_ifs <;> fun_prop

lemma gauge_fermion (k : Lat.Frame n) (U : Grid n) : B.fermion (gauge k U) =
    rotates N k * B.fermion U * star (rotates N k) := by
  simp_rw [fermion,bareD_covariant]
  unfold rotates copies
  rw [block_star,← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]

lemma gauge_gauss (k : Lat.Frame n) (U : Grid n) : slots N k (Grass.gauss (B.fermion (gauge k U))) =
    Grass.gauss (B.fermion U) := by
  rw [slots,Grass.gauss_map, Matrix.transpose_transpose,B.gauge_fermion]; congr 1
  have hg := (rotates_law N k).1
  rw [Matrix.mul_assoc (rotates N k * _), hg, Matrix.mul_one, ← Matrix.mul_assoc, hg, Matrix.one_mul]

theorem continuous_weight : Continuous B.weight := by
  unfold weight; fun_prop

lemma integrable_weight : Integrable B.weight (prior su n) :=
  B.continuous_weight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma weight_complex (U : Grid n) : B.weight U = (bare B.beta U : ℂ) • Grass.gauss (B.fermion U) :=
  RCLike.real_smul_eq_coe_smul (K:=ℂ) ..

lemma gauge (k : Lat.Frame n) (U : Grid n) : slots N k (B.weight (Lattice.gauge k U)) = B.weight U := by
  rw [weight_complex, Wilson.bare_gauge, map_smul,B.gauge_gauss,B.weight_complex]

lemma plus (U : Grid n) : Grass.Plus (B.weight U) := by
  have h := Grass.gauss_plus (B.fermion U)
  unfold Grass.Plus at *; rw [B.weight_complex, map_smul,h]

/-- Berezin top coefficient integrated at fixed gauge. -/
lemma determinant (U : Grid n) : Grass.ber _ (B.weight U) =
    (bare B.beta U : ℂ) * ∏ i : Flavor N, (bareD B.seam U (B.mass i)).det := by
  rw [weight_complex,map_smul,Grass.det_amplitude,trace_det, smul_eq_mul]

def marginal (U : Grid n) : ℝ := bare B.beta U * ∏ i : Flavor N, (bareD B.seam U (B.mass i)).det.re

lemma at_pair (U : Grid n) : Grass.ber _ (B.weight U) = (B.marginal U : ℂ) := by
  rw [determinant,marginal]; simp_rw [Complex.ofReal_mul,Complex.ofReal_prod,realD]

def partition : ℝ := ∫ U, B.marginal U ∂prior su n

@[fun_prop] theorem continuous_marginal : Continuous B.marginal := by
  unfold marginal; fun_prop
lemma marginal_integrable : Integrable B.marginal (prior su n) :=
  B.continuous_marginal.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem volume : Density.volume B.weight = ↑B.partition := by
  unfold Density.volume partition; simp_rw [at_pair,integral_complex_ofReal]

/-! ## Exact re-expression for RP -/

def massMatrix : Matrix (Modes n N) (Modes n N) ℂ :=
  Matrix.blockDiagonal fun l : Flavor N => (B.mass l : ℂ) • (1 : Sheet n)

theorem ferm_eq (U : Grid n) : B.fermion U = B.starter.ferm U + B.massMatrix := by
  have h (l : Flavor N) : bareD B.seam U (B.mass l) =
      bareD B.seam U 0 + (B.mass l : ℂ) • 1 := by
    simp [bareD]; abel
  unfold massMatrix; change Matrix.blockDiagonal _ = Matrix.blockDiagonal (fun _ => bareD B.seam U 0) + _
  rw [← Matrix.blockDiagonal_add]
  exact congrArg Matrix.blockDiagonal (funext h)

def factor : Insertion n N := ContinuousMap.const _ (Grass.gauss B.massMatrix)

theorem integrand (x : Insertion n N) (U : Grid n) :
    Grass.ber _ ((B.weight * ⇑x) U) = B.starter.rate (B.factor*x) U := by
  rw [Pi.mul_apply, B.weight_complex, ferm_eq,Grass.gauss_add]
  simp only [smul_mul_assoc, map_smul, smul_eq_mul]
  change _= _*Grass.ber _ (Grass.gauss (B.starter.ferm U) * (Grass.gauss B.massMatrix * x U)); rw [mul_assoc]; rfl

theorem moment_eq (x : Insertion n N) : Density.moment B.weight x = B.starter.raw (B.factor*x) := by
  unfold Density.moment Density.volume; simp_rw [integrand]; rfl

theorem moment_uniform (C : Cut n N) (x : Insertion n N) : Density.moment (uniform C).weight x = C.raw x := by
  change (∫ U, Grass.ber (Modes n N) (((uniform C).weight * ⇑x) U) ∂prior su n) = ∫ U, _ ∂prior su n
  congr 1; funext U; rw [Pi.mul_apply,weight_complex]; simp only [smul_mul_assoc,map_smul,smul_eq_mul]; rfl

theorem partition_uniform (C : Cut n N) : (uniform C).partition = C.partitionR := by
  apply Complex.ofReal_injective; rw [← volume,← Cut.raw_one,← moment_uniform,Density.moment]
  change _ = Density.volume (_ * 1); rw [mul_one]

end Torus
end YM.TorusPCAC
