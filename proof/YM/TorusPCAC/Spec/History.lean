import YM.TorusPCAC.Spec.Regulator
import YM.QCD.Flume.Collect
import YM.QCD.Step.Wrapper
import YM.RG.Block

/-!
# One joint block history: calibration target

Use one schedule and one *sequence* of space-periods in the target. At
index `q` block the Wilson input at depth `N = depth q` by the actual
shared tag choices, through `m=N,N-1,...,0`. `beta q m` is the tag at
level `m` (at N it's also the bare gauge weight); on split trajectories
use approximate kinetic matching, not demand e.g. that the representation
of its flags or perturbing E/K terms be unique. This choice of Wilsonian
scheme tests the tag directly on the **actual** effective density (including
at scale zero) to small absolute accuracy chosen before the existence
problem. It doesn't demand the specific price arrays and zero-jet
conventions of the proposed construction; see `work/bend.tex` and the
notes on the specification. Every positive eta-demand will be included.

We ask also for a normalization and mass read of the effective spin fields
at scale 0 (using the short window `VA` approach the estimate will need to
be small *even compared with the splitting* there). These readouts are
taken on the same densities. No ghost arm/quenched measure, no assumptions
about positivity of the fermion determinant pointwise.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC
open Lattice Wilson QCD QCD.Lat MeasureTheory Filter RG
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ComplexOrder

/-- Use `Flume.tied`; the kernel `Q` doesn't depend on the wing. -/
def prototype (P : Patch) : YM.Next.Free.Flight P.J P.J :=
  ⟨P.L,P.odd_side,P.coarse,P.order_cut,le_rfl,by omega,.top _⟩

variable {c f : Side} {N : ℕ}

def meanSpin (J : StepData c f) (U : Grid f) : Matrix (Modes c N) (Modes f N) ℂ :=
  -- block diagonal (rectangular)
  Matrix.blockDiagonal (fun _ : Fin N => Flume.tied (prototype J.patch) J.sizes 0 U)

def rescaleSpin (w : ℝ) : Fields c N →ₐ[ℂ] Fields c N := Grass.adapter ((w:ℂ) • 1) ((w:ℂ) • 1)

def high (J : StepData c f) (X : Density f N) (U : Grid f) : Fields c N :=
  Kit.sheath 1 (meanSpin J U) (X U)

def block (J : StepData c f) (b w : ℝ) (X : Density f N) : Density c N :=
  fun V => rescaleSpin w (J.push b (high J X) V)

/-- The same transport for arbitrary continuous density inputs (also odd).
Explicitly demand well-defined integrals and full Berezin normalization. -/
def NormalizedStep (J : StepData c f) (b w : ℝ) (N : ℕ) : Prop :=
  J.IsKernel b su ∧
  ∀ X : Density f N, Continuous X → (∀ V : Grid c,
    Integrable (fun U => J.density b U V • high J X U) (prior su f)) ∧
    Continuous (block J b w X) ∧ Density.volume (block J b w X) =
      (w:ℂ)^(2 * Fintype.card (Modes c N)) * Density.volume X

/-- Geometry and scalar choices for all these tori. `N` here on History is
**flavor count**. For notational convenience give tag data also above
`depth`: no uses in the target. -/
structure History (N : ℕ) where
  S : Schedule
  depth : ℕ → ℕ
  depthGrow : StrictMono depth
  K : KernelChoices
  patch (m : ℕ) : Patch
  sized (m) : (patch m).L = S.block m
  branches (m) : (patch m).Branches K su
  beta (q m : ℕ) : ℝ
  w (q m : ℕ) : ℝ  -- rescaling *after* step m+1 → m
  mass (q : ℕ) : Flavor N → ℝ

namespace History
variable (H : History N)
abbrev lattice (m q) := H.S.side m q
abbrev UV (q) := H.lattice (H.depth q) q
def step (m q : ℕ) : StepData (H.lattice m q) (H.lattice (m+1) q) :=
  ⟨H.patch m,H.K,by rw [H.sized m]; exact (H.S.oneStep m q).exact_size⟩

def push (H : History N) (q : ℕ) (m M : ℕ) : Density (H.lattice M q) N → Density (H.lattice m q) N :=
  if h0 : M = m then fun X => by subst M; exact X
  else
    if _hg : m < M then fun X => block (H.step m q) (H.beta q (m+1)) (H.w q m) (push H q (m+1) M X)
    else fun _ => 0
termination_by M-m

/-- One Wilson--fermion input at each depth. -/
def start (q : ℕ) : Torus (H.UV q) N := ⟨0,H.beta q (H.depth q),H.mass q⟩

def actual (q m : ℕ) : Density (H.lattice m q) N :=
  H.push q m (H.depth q) (H.start q).weight

end History

/-- Metric `-(1/3) tr(T T')`; in this metric C_A=18. -/
def rate : ℝ := 11 * 18 / (24*Real.pi^2) - 6 / (2*Real.pi^2)

namespace History

/-- Tests for the tagged massive history, on one beta window. These fields
are named to distinguish achieved milestones from the target. They are NOT
assumptions authorized towards existence.

`scale m = log a_m⁻¹`. `S.period q → infinity`, four multiple,
`S.shrinks : S.a → 0` with `S.a 0 = 1`; see `Lattice/Scale.lean`.
Require at least one step also on every selected regulator. -/
structure Calibrated (H : History 6) (ell η : ℝ) (u : Fin 6 → ℝ) : Prop where
  startsLater (q) : 0 < H.depth q
  bareSplit (q) : Function.Injective (H.mass q)
  runsWeak : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    ∀ q : ℕ, m ≤ H.depth q → |H.beta q m / H.S.scale m - rate| < ε
  af : 0 < rate
  root (q) : H.beta q 0 = ell
  positive (q m) (h : m ≤ H.depth q) : 0 < H.beta q m
  scales (q m) (h : m < H.depth q) : 0 < H.w q m
  normalization (q m) (h : m < H.depth q) :
    NormalizedStep (H.step m q) (H.beta q (m+1)) (H.w q m) 6
  continuousDensity (q m) (h : m ≤ H.depth q) : Continuous (H.actual q m)
  sea (q m) (h : m ≤ H.depth q) : ∃ v : ℝ, 0 < v ∧ Density.volume (H.actual q m) = ↑v
  even (q m) (h : m ≤ H.depth q) (U) : Grass.Plus (H.actual q m U)
  logarithm (q m) (h : m ≤ H.depth q) : ∀ᶠ U in 𝓝 (1 : Grid (H.lattice m q)),
    IsUnit (H.actual q m U) ∧
    ∃ b : ℝ, 0 < b ∧ Density.body (H.actual q m) U = ↑b
  kinetic (q m) (h : m ≤ H.depth q) : Density.KineticMatch η (H.beta q m) (H.actual q m)
  /-- Also an actual fixed-scale inverse coupling read exists, rather than
  e.g. escaping to infinity with the cutoffs. The numerical equality with
  `ell` is **not** a requirement; `ell` is in the Wilsonian step scheme. -/
  atReference : ∃ b : ℝ, 0 < b ∧ |b - ell| ≤ η ∧
    ∀ (i a : Axis), i ≠ a → ∀ T : su.Color, ‖T‖ = 1 →
      Tendsto (fun q => Density.kineticGauge (H.actual q 0) i a T) atTop (𝓝 b)
  commonColors : ∃ T : su.Color, ‖T‖ = 1
  /-- additional Wilsonian mass and normalization read; see work/massread. -/
  symbol (s : Axis → Bool) (l : Fin 6) :
    Tendsto (fun q => Density.massesProbe (H.actual q 0) s l) atTop (𝓝 ((u l : ℂ) • (1:Bundle)))
  slash (s : Axis → Bool) (l : Fin 6) (i : Axis) : ∀ᶠ q : ℕ in atTop,
    ‖Density.kineticFermion (H.actual q 0) s l i - Complex.I • Lat.wave (gamma i)‖ ≤ η

end History
end YM.TorusPCAC
