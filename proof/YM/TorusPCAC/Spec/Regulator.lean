import YM.QCD.Lattice.Cut
import YM.QCD.Grass.SD
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# TorusPCAC-QCD target: Wilson regulator and coupling/mass readouts

Part of the **statement**, not postulates/lemmas asserting a physical limit.
See `Target.lean`. Use `YM.QCD` Pauli, transporter, gamma5 and Berezin
conventions (not `YM.QCDVacuum`). Dimension four, seams of the *physics
target* at coordinate zero; give `torus` defs for arbitrary AP seam.

A beta tag in the target history will be a Wilsonian block parameter (in
addition to the parameter of the literal Wilson input). To specify the
accuracy of this coupling scheme we follow `work/bend.tex`, paragraph
"approximate kinetic read", with the body Hessian on unit-amplitude
opposite plane waves, **not** require a particular internal representation
by price masks or uniqueness of the beta tag. This uses actual densities
before integrating out fermions (ordinary body, not Berezin amplitude).
The representative `ell` at scale zero and any intervals around it in the
specification have no claimed interpretation as an exact determination of,
e.g., a scattering coupling.

There is also a read of the actual `ψ ψbar` coefficient at identity links;
at scale 0 the target includes a normalization of the kinetic term there
and uses near-zero AP momenta to observe the Wilsonian masses. These will
not be the *definition* of `mᵢ^ren`. See the separate PCAC requirement.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC
open Lattice Wilson MeasureTheory QCD QCD.Lat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ComplexOrder

/-- Keep flavor count as an index in regulator lemmas. Use `N=6`
simultaneously in all regulator and continuum assertions of the target. -/
abbrev Density (n : Side) (N : ℕ) := Grid n → Fields n N

structure Torus (n : Side) (N : ℕ) where
  seam : Site n
  beta : ℝ
  mass : Flavor N → ℝ

variable {n : Side} {N : ℕ}

namespace Torus

variable (B : Torus n N)

/-- Direct sum in flavor *at the same gauge argument*. -/
def fermion (U : Grid n) : Matrix (Modes n N) (Modes n N) ℂ :=
  Matrix.blockDiagonal (fun l => bareD B.seam U (B.mass l))

/-- Actual Wilson/Berezin weight, against normalized Haar on links. -/
def weight : Density n N := fun U => bare B.beta U • Grass.gauss (B.fermion U)

end Torus

namespace Density

def volume (ρ : Density n N) : ℂ := ∫ U, Grass.ber (Modes n N) (ρ U) ∂prior su n

def moment (ρ X : Density n N) : ℂ := volume (ρ * X)

/-- Require integrability of weighted insertions and positivity of volume
for uses in the target. -/
def normalize (ρ X : Density n N) : ℂ := moment ρ X / volume ρ

/-- The scalar site-free (zero Grassmann degree) coefficient. -/
def body (ρ : Density n N) (U : Grid n) : ℂ := Grass.coef ∅ (ρ U)

/-- Used at seam zero when reading the target history. -/
def transversePlane (T : su.Color) (f : ℝ → ℝ) (i a : Axis) (h : ℝ) : Grid n := fun e =>
  if e.2 = i then
    su.lieExp ((h * f (2 * Real.pi / n.val * ((e.1 a).val : ℝ))) • T)
  else 1

def probeGauge (ρ : Density n N) (i a : Axis) (T : su.Color) (f : ℝ → ℝ) (h : ℝ) :=
  - Real.log (body ρ (transversePlane T f i a h)).re

/-- Bill in the Wilsonian Hessian-matching scheme. In addition check that
we're in the positive-body neighborhood and enough differentiability. -/
def kineticGauge (ρ : Density n N) (i a : Axis) (T : su.Color) : ℝ :=
  (iteratedDeriv 2 (probeGauge ρ i a T Real.cos) 0 +
   iteratedDeriv 2 (probeGauge ρ i a T Real.sin) 0) /
  (Fintype.card (Site n) * (2 * Real.pi / n.val)^2)

def KineticMatch (η beta : ℝ) (ρ : Density n N) : Prop :=
  ∀ (i a : Axis), i ≠ a → ∀ T : su.Color, ‖T‖ = 1 →
    ContDiffAt ℝ 2 (probeGauge ρ i a T Real.cos) 0 ∧
    ContDiffAt ℝ 2 (probeGauge ρ i a T Real.sin) 0 ∧
    |kineticGauge ρ i a T - beta| ≤ η

/-- `exp(- ψbar M ψ + other degrees)` on no-odd, nonzero body at trivial
links. Read `M`, using left Grassmann derivatives. Zero here if used
outside that setup with zero body; target forbids such use. -/
def bilinear (ρ : Density n N) (i j : Modes n N) : ℂ :=
  - Grass.coef ∅ (Grass.vary (.inl j) (Grass.vary (.inr i) (ρ 1))) / body ρ 1

/-- Lowest AP momenta `π/n * ±`. -/
def ap (n : Side) (s : Axis → Bool) (i : Axis) : ℝ :=
  if s i then Real.pi / n.val else -Real.pi / n.val

/-- AP wave uses nonnegative representatives (seams at zero). -/
def phase (n : Side) (p : Axis → ℝ) (x : Site n) : ℂ :=
  Complex.exp (Complex.I * ↑(∑ i, p i * (((x i).val : ℕ) : ℝ)))

/-- Per-site-volume testing, without summing over flavor. -/
def symbol (ρ : Density n N) (p : Axis → ℝ) (l : Flavor N) : Bundle := Matrix.of fun i j =>
  (∑ x : Site n, ∑ y : Site n, star (phase n p x) *
    bilinear ρ ((x,i),l) ((y,j),l) * phase n p y) / Fintype.card (Site n)

def massesProbe (ρ : Density n N) (s : Axis → Bool) (l : Flavor N) : Bundle :=
  symbol ρ (ap n s) l

/-- Difference of near-zero probes flip one sign, divided by that momentum
difference. Missing mass identity alone (e.g. unnormalized spin) isn't this
kinetic probe. It's useful at the reference step; all these readouts are
on the unselected finite densities. -/
def kineticFermion (ρ : Density n N) (s : Axis → Bool) (l : Flavor N) (a : Axis) : Bundle :=
  (((2 * Real.pi / n.val : ℝ) : ℂ)⁻¹) •
    (massesProbe ρ (Function.update s a true) l - massesProbe ρ (Function.update s a false) l)

end Density

end YM.TorusPCAC
