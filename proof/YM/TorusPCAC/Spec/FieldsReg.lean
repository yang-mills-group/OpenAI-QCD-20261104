import YM.TorusPCAC.Spec.History
import YM.TorusPCAC.Spec.Jet
import YM.Source.Local

/-!
# Calibration of the *actual* primaries

Regulator origins and taper about `0` on the cover. Require exactly the
Taylor tests (use `h` in this file for the scaling indeterminate λ¹ᐟ²,
NOT the letter budget; tests through doubled engineering weight d) on the
relative inserted effective density. This ties all calibrations to the
same genuine finite-volume history. A fixed local stencil section for each
d, independent of regulators (poly in entries, exterior in spin). Physical
placement uses the lift with AP signs, oriented as the bare action.

Can take references e.g. on sufficiently smooth plateaus. Conventions:
we specify coordinates as ordinary jets of the **physical** insertion at
that reference step. In the candidate, conversion is to the scaled
coordinates there, multiplying also by `a_ref^D` if necessary when using
that horizon's counting-unit conventions. In particular at the level-0
calibration the lattice unit there is *one*: the label selecting a current
or density for the PCAC test is just the unweighted symbol.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC
open Set QCD QCD.Lat Jet Wilson Lattice Filter Function
open scoped TensorProduct Topology BigOperators ContDiff Matrix.Norms.Frobenius

/-- Coords in *lattice units*. -/
def coords (x : Cover) : E4 := WithLp.toLp 2 (fun i => (x i : ℝ))

/-- AP seam zero (`-` on hop -1 to 0 in each direction). -/
def thermal (n : Side) (x : Cover) : ℂ :=
  ∏ i, (-1:ℂ)^(x i / n.val)

/-- An actual averaging convention on the origin stencil at **all levels**. -/
inductive Primary
  | point
  | average (r : Axis → Fin 7)

namespace Primary

def along {V : Type*} [AddCommMonoid V] [Module ℂ V] (M : Side) (s : ℕ)
    (i : Axis) (f : Cover → V) (x : Cover) : V :=
  let m : ℤ := (M.val/2 : ℕ)
  (M.val:ℂ)⁻¹ • ∑ z ∈ Finset.Icc (-m) m, f (x + ((s:ℤ)*z) • Lattice.step i)

def boxes {V : Type*} [AddCommMonoid V] [Module ℂ V] (M : Side) (r : Axis → Fin 7) (i : Axis)
    (f : Cover → V) : Cover → V :=
  along M 1 i ((along M 2 i)^[ (r i).val ] f)

def atOrigin {V : Type*} [AddCommMonoid V] [Module ℂ V] (H : Primary) (M : Side)
    (f : Cover → V) : V :=
  match H with
  | .point => f 0
  | .average r => ((List.ofFn (id : Axis → Axis)).foldr (fun i g => boxes M r i g) f) 0

def turned (u : Primary) (g : Signed) : Primary :=
  match u with
  | point => point
  | average r => average (r ∘ g.perm.symm)

end Primary

namespace Read

structure Taper where
  χ : E4 → ℝ
  smooth : ContDiff ℝ ∞ χ
  range (x) : χ x ∈ Icc 0 1
  cutoff (x : E4) : 1/4 ≤ cubedist x 0 → χ x = 0
  interior (x : E4) : cubedist x 0 ≤ 1/8 → χ x = 1
  turns (s : Signed) (x : E4) : χ (Ortho.move s.ortho x) = χ x

def location (l : Edge Cover) (v : ℝ) : E4 := coords l.1 + v • basis l.2

def fade (C : Taper) (n : Side) (z : E4) := C.χ ((n.val:ℝ)⁻¹ • z)

def connection (C : Taper) (n : Side) (d : ℕ) (A : Labels.Jet su) (h : ℝ)
    (l : Edge Cover) (v : ℝ) :=
  fade C n (location l v) • Source.partConnection (d/2) A (h^2) l v

structure Chart where
  taper : Taper
  flow (n : Side) (d : ℕ) (A : Labels.Jet su) (h : ℝ) (l : Edge Cover) : ℝ → su.El
  solves n d A h l : Source.SolvesLink (flow n d A h l) (connection taper n d A h l)

def link (C : Chart) (n : Side) (d : ℕ) (A : Labels.Jet su) (h : ℝ) : Grid n :=
  fun l => C.flow n d A h (Lattice.lift l.1,l.2) 1

def coefficient (b : Jet.Order) (x : E4) : ℂ :=
  ∏ i : Axis, (x i : ℂ)^(b i) / (b i).factorial

def bounded (d : ℕ) : Finset Jet.Order := by
  classical
  exact (Fintype.piFinset fun _ : Axis => Finset.range (d+1)).image Finsupp.equivFunOnFinite.symm

def scale (h : ℝ) (v : Letter) := (h:ℂ)^(spinOrder v)

variable {K : ℕ}
abbrev External := Grass.Seed (Fin K)

def probe (C : Chart) (d : ℕ) (x : Letter → External (K:=K)) (h : ℝ)
    {n : Side} (m : Modes n 6) (k : Kind) : External (K:=K) :=
  let o := Lattice.lift m.1.1
  let z := coords o
  let f b : Letter := ⟨k,m.2,m.1.2.1,m.1.2.2,b⟩
  ((fade C.taper n z : ℂ) * thermal n o) • ∑ b ∈ bounded d,
    (if spinOrder (f b) ≤ d then (scale h (f b) * coefficient b z) • x (f b) else 0)

def examine (C : Chart) (d : ℕ) (x : Letter → External (K:=K)) (h : ℝ)
    {n : Side} : Fields n 6 →ₐ[ℂ] Grass.Alg (Fin K) := ExteriorAlgebra.map
  ((Grass.thetaBasis _).constr ℂ (Sum.elim (fun i => probe C d x h i .col) (fun i => probe C d x h i .row)))

def evaluate (A : Labels.Jet su) (x : Letter → External (K:=K)) (h : ℝ) :
    Pol →ₐ[ℂ] Grass.Alg (Fin K) := (Algebra.TensorProduct.lid ℂ (Grass.Alg (Fin K))).toAlgHom.comp
  (Algebra.TensorProduct.map (Labels.read (Source.scaleJet A (h^2)))
    (ExteriorAlgebra.map (Finsupp.lift _ _ _ fun l : Letter => scale h l • x l)))

def Reads {n : Side} (C : Chart) (d : ℕ) (v : Label d) (X : Density n 6) :=
  ∀ (K : ℕ) (x : Letter → External (K:=K)) (A : Labels.Jet su),
   let F := fun h : ℝ => examine C d x h (X (link C n d A h))
   let P := fun h : ℝ => evaluate A x h v.val
   ContDiffAt ℝ (d : ℕ∞) F 0 ∧ ContDiffAt ℝ (d : ℕ∞) P 0 ∧
   ∀ j ≤ d, iteratedDeriv j F 0 = iteratedDeriv j P 0

end Read

namespace Stencil

abbrev Mode (X : Finset Cover) := ((↥X × Lat.Fiber) × Jet.Flav)

abbrev Formula (X : Finset Cover) := Source.Formula su X ⊗[ℂ] Grass.Dirac (Mode X)

variable {n : Side} {X : Finset Cover}

def seed (x : Cover) (k : Mode X) (ι : Modes n 6 → Grass.Pairs (Modes n 6)) : Grass.Seed (Grass.Pairs (Modes n 6)) :=
  thermal n (x + k.1.1.val) • Grass.thetaBasis (Grass.Pairs (Modes n 6)) (ι ((wrap n (x + k.1.1.val), k.1.2), k.2))

def place (U : Grid n) (x : Cover) : Formula X →ₐ[ℂ] Fields n 6 :=
  (Algebra.TensorProduct.lid ℂ (Fields n 6)).toAlgHom.comp
    (Algebra.TensorProduct.map
      (MvPolynomial.aeval (Source.entry (expandAt (wrap n x) U)))
      (ExteriorAlgebra.map ((Grass.thetaBasis _).constr ℂ
        (Sum.elim (fun i => seed x i Sum.inl) (fun i => seed x i Sum.inr)))))

def asDensity (x : Cover) (p : Formula X) : Density n 6 := fun U => place U x p

/-- Lattice flavor and gauge on regulator fields/densities. -/
def flavorMatrix (n : Side) (u : FlavorGroup) : Matrix (Modes n 6) (Modes n 6) ℂ :=
  Matrix.diagonal (fun i => (u i.2 : ℂ))
def rotateFlavor (n : Side) (u : FlavorGroup) :=
  Grass.adapter (flavorMatrix n u) (star (flavorMatrix n u))

/-- Entrywise conjugation on links, to be used along with **linear** C on
Grassmann generators. -/
def conjSU (U : su.El) : su.El :=
  let A : Mat := su.mat U
  let V := QCD.which true A
  ⟨⟨V, by
    refine ⟨?_,?_⟩
    · change star (QCD.which true A) * QCD.which true A = _
      rw [QCD.which_star, ← QCD.which_mul, show star A * A = 1 from su.mat_star_mul U,
        QCD.which_one]; rfl
    change QCD.which true A * star (QCD.which true A) = _
    rw [QCD.which_star, ← QCD.which_mul, show A * star A = 1 from su.mat_mul_star U,
      QCD.which_one]; rfl⟩, by
    change (Matrix.map _ _).det = 1
    have e := RingHom.map_det (starRingEnd ℂ) (su.mat U)
    rw [det_su,map_one] at e; exact e.symm⟩

def conjGrid (U : Grid n) : Grid n := conjSU ∘ U

/-- Exchange columns with rows at the same site/color/flavor. Matrices
specified acting on column of ψ's (point index k transforms by `S k i`)
and row of bars respectively. -/
def spinChange {N : ℕ} (n : Side) (S T : Spike) : Fields n N →ₐ[ℂ] Fields n N :=
  Grass.changeVars (Matrix.fromBlocks 0 (Lat.copies N (onSpin n S))
    (Lat.copies N (onSpin n T)).transpose 0)

def charge (n : Side) {N : ℕ} : Fields n N →ₐ[ℂ] Fields n N := spinChange n Cmat (-Cmat⁻¹)
def five (n : Side) {N : ℕ} : Fields n N →ₛₗ[starRingEnd ℂ] Fields n N :=
  (spinChange n g5.transpose (-g5.transpose)).toLinearMap.comp Grass.cc

/-- Convert the nonnegative rep of a site to the cover in our seam-zero convention. -/
def nonnegative (x : Site n) : Cover := fun a => (x a).val

/-- Substitution on ψ and bars along the Pin lifts of the signed-coordinate
group, with moves about the origin in this lift. The orientation factor is
for the seam-zero convention. -/
def move (s : Signed) (p : Spin.Pin) {N : ℕ} : Fields n N →ₐ[ℂ] Fields n N :=
  let R (A : Spike) : Sheet n := Matrix.of fun u v =>
    let o := s.act (nonnegative (n:=n) u.1)
    if wrap n o = v.1 then thermal n o * wave A u.2 v.2 else 0
  Grass.adapter (Lat.copies N (R p.val.2⁻¹.val)) (Lat.copies N (R p.val.2.val.transpose))

/-- Fixed local representation of the *jet*, before imposing the renormalizations.
This forecloses, for instance, just multiplying some other sequence by huge
parameters after reading it back at the normalization step and calling it
the primary (same stencils whether point or averaged-reference readout).
Doesn't require a canonical choice independent of all regulator parameters;
it's chosen for the given theory, but *one* such for the family. -/
structure Representation (d : ℕ) where
  shape : Finset Cover
  columns : Label d →ₗ[ℂ] Formula shape

/-- Taper/jet and unit tests, on the actual sequence of bare tori. -/
structure Section (H : History 6) (C : Read.Chart) {d : ℕ} (P : Representation d) : Prop where
  root : 0 ∈ P.shape
  turns (g : Signed) : P.shape.image (Signed.act g) = P.shape
  unit (p : Label d) (hp : p.val=1) : P.columns p = 1
  reads : ∀ᶠ q : ℕ in atTop, ∀ x, Read.Reads (n:=H.UV q) C d x (asDensity 0 (P.columns x))

end Stencil

/-- All point and averaging calibrations, not yet quotienting the labels. -/
structure ChartData (H : History 6) where
  chart : Read.Chart
  ref (d : ℕ) : ℕ
  representation (d : ℕ) : Stencil.Representation d
  map (q d : ℕ) (u : Primary) : Label d ≃ₗ[ℂ] Label d

namespace ChartData

variable {H : History 6} (P : ChartData H)

def primary (q d : ℕ) (u : Primary) (v : Label d) (x : Cover) : Density (H.UV q) 6 :=
  Stencil.asDensity x ((P.representation d).columns (P.map q d u v))

def dilate (q : ℕ) (m : ℕ) := H.S.steps m (H.depth q - m)

def exert (q d : ℕ) (u : Primary) (v : Label d) (m : ℕ) : Density (H.lattice m q) 6 :=
  H.push q m (H.depth q) ((H.start q).weight *
    (u.atOrigin (dilate (H:=H) q m) (fun x => P.primary q d u v x)))

def projection (q d : ℕ) (u : Primary) (v : Label d) : Density (H.lattice (P.ref d) q) 6 :=
  fun U => Ring.inverse (H.actual q (P.ref d) U) * P.exert q d u v (P.ref d) U

/-- Flavor and gauge on the UV system; impose actual symmetry (also on the effective
vacuum system as it is transmitted: `slots`, `rotateFlavor` apply at that
level). -/
structure Regulators (H : History 6) : Prop where
  flavor (u : FlavorGroup) (q m : ℕ) (h : m ≤ H.depth q) (U : Grid (H.lattice m q)) :
    Stencil.rotateFlavor _ u (H.actual q m U) = H.actual q m U
  gauge (q m : ℕ) (h : m ≤ H.depth q) (U : Grid (H.lattice m q)) (k : Frame (H.lattice m q)) :
    slots 6 k (H.actual q m (Lattice.gauge k U)) = H.actual q m U

  charge (q m) (h : m ≤ H.depth q) (U) :
    Stencil.charge _ (H.actual q m (Stencil.conjGrid U)) = H.actual q m U
  reality (q m) (h : m ≤ H.depth q) (U) : Stencil.five _ (H.actual q m U) = H.actual q m U
  signed (p : Spin.Pin) (s : Signed) (he : p.val.1 = s.ortho) (q m) (h : m ≤ H.depth q) (U) :
    Stencil.move s p (H.actual q m (pull s 0 U)) = H.actual q m U

/-- Use the physical sizes of these further volume demands by eventuality in q.
Actual near-identity tests, not a formal read based just on the flat model. -/
structure Based : Prop where
  startScale (d : ℕ) (h : d ≤ 8) : P.ref d = 0
  sectionMaps (d : ℕ) : Stencil.Section H P.chart (P.representation d)
  physical (d : ℕ) (u : Primary) : ∀ᶠ q : ℕ in atTop,
    P.ref d ≤ H.depth q ∧ (∀ v : Label d,
     Read.Reads P.chart d v (P.projection q d u v) ∧
     ∀ (x : Cover), (v.val = 1 → P.primary q d u v x = 1) ∧
       Continuous (P.primary q d u v x) ∧ ∀ (U : Grid (H.UV q)),
       (∀ k, slots 6 k (P.primary q d u v x (Lattice.gauge k U)) = P.primary q d u v x U) ∧
       (∀ (z : FlavorGroup) (w : Label d), w.val = Jet.flavor z v.val →
         Stencil.rotateFlavor (H.UV q) z (P.primary q d u v x U)=P.primary q d u w x U) ∧
       (∀ w : Label d, w.val = Jet.grade v.val →
         Grass.grade (P.primary q d u v x U) = P.primary q d u w x U) ∧
       (∀ w : Label d, w.val = Jet.charge v.val →
         Stencil.charge _ (P.primary q d u v x (Stencil.conjGrid U)) = P.primary q d u w x U) ∧
       (∀ w : Label d, w.val = Jet.five v.val →
         Stencil.five _ (P.primary q d u v x U) = P.primary q d u w x U) ∧
       (∀ (w : Label d) (p : Spin.Pin) (s : Signed), p.val.1=s.ortho → w.val = Jet.rotate p v.val →
         Stencil.move s p (P.primary q d u v x (pull s 0 U)) = P.primary q d (u.turned s) w (s.act x) U))
  orbit : Regulators H

end ChartData
end YM.TorusPCAC
