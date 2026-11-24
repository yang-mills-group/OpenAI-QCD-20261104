import YM.TorusPCAC.Spec.Spin
import YM.Gauge.Colors
import YM.Labels.Action
import YM.QCD.Matter
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Analysis.Complex.Circle

/-!
# Label space of the massive-QCD target

Use YM's independent gauge Taylor variables (`Labels.Taylor`). All actual
color tensors use `colorIso` and that normalization. Add the exterior
algebra of **independent** row/column jets of 6 four-component, three-color
Dirac fields (radial gauge, symmetric covariant Taylor indices). The cap
on a polynomial is *engineering weight*, not the number of factors. We
work in doubled weights `d=2D`. Nothing in this source-space throws away
equations or tests flavor neutrality or evenness.

Color transformations here are residual at the radial-gauge base, not
on-site gauge transformations on finite raw stencils. Spin variables are
the symmetric derivatives **without** Taylor factorials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC
open QCD QCD.Lat MvPolynomial
open scoped Topology TensorProduct Matrix.Norms.Frobenius BigOperators Kronecker
namespace Jet

abbrev Flav := Fin 6
abbrev FlavorGroup := Flav → Circle
abbrev Order := Axis →₀ ℕ

/-- Column `ψ` or row `bar`, respectively (independent generators). -/
inductive Kind
  | col | row
  deriving Fintype, DecidableEq

structure Letter where
  kind : Kind
  flavor : Flav
  spin : Pinor
  color : Hue
  derivatives : Order

noncomputable instance letterOrder : LinearOrder Letter := by
  classical exact linearOrderOfSTO WellOrderingRel

abbrev Bos := Labels.Pol su
abbrev Raw := Letter →₀ ℂ -- one-leg spin space
abbrev GrassJet := ExteriorAlgebra ℂ Raw
abbrev Pol := Bos ⊗[ℂ] GrassJet

abbrev fermBasis : Module.Basis Letter ℂ Raw := Finsupp.basisSingleOne

def monomial : Module.Basis ((Labels.Key su →₀ ℕ) × Finset Letter) ℂ Pol :=
  (basisMonomials (Labels.Key su) ℂ).tensorProduct fermBasis.ExteriorAlgebra

def gOrder (b : Labels.Key su →₀ ℕ) := 2 * Labels.height b
def spinOrder (l : Letter) := 3 + 2 * ∑ a, l.derivatives a
def orders (k : (Labels.Key su →₀ ℕ) × Finset Letter) := gOrder k.1 + ∑ l ∈ k.2, spinOrder l

def cap (d : ℕ) : Submodule ℂ Pol := Submodule.span ℂ ((⇑monomial) '' {k | orders k ≤ d})

def spinMap (f : Letter → Raw) : GrassJet →ₐ[ℂ] GrassJet := ExteriorAlgebra.map (Finsupp.lift Raw ℂ _ f)

def point (x : Letter) : Raw := Finsupp.single x 1

def paint (U : su.El) : Pol →ₐ[ℂ] Pol := Algebra.TensorProduct.map
  (Labels.changed fun _ => Labels.Taylor.paint U)
  (spinMap fun l => ∑ i : Hue,
    (if l.kind = .col then su.mat U l.color i else (su.mat U⁻¹) i l.color) •
      point { l with color := i })

def invariant : Submodule ℂ Pol := ⨅ U : su.El, LinearMap.ker ((paint U).toLinearMap - LinearMap.id)

def admitted (d : ℕ) : Submodule ℂ Pol := cap d ⊓ invariant

abbrev Label (d : ℕ) := ↥(admitted d)

def rotateMono (R : Ortho) (l : Order) : MvPolynomial Axis ℂ :=
  ∏ a : Axis, (∑ i : Axis, C (R.val i a : ℂ) * X i)^ (l a)

def rotate (p : Spin.Pin) : Pol →ₐ[ℂ] Pol := Algebra.TensorProduct.map (Labels.rotated p.val.1)
  (spinMap fun l => ∑ t ∈ (rotateMono p.val.1 l.derivatives).support, ∑ s : Pinor,
    ((rotateMono p.val.1 l.derivatives).coeff t *
      (if l.kind = .col then (p.val.2⁻¹).val l.spin s else p.val.2.val s l.spin)) •
        point { l with spin := s, derivatives := t })

def grade : Pol →ₐ[ℂ] Pol := Algebra.TensorProduct.map (AlgHom.id ℂ Bos)
  (spinMap fun l => -point l)

def flavor (u : FlavorGroup) : Pol →ₐ[ℂ] Pol := Algebra.TensorProduct.map (AlgHom.id ℂ Bos)
  (spinMap fun l => (if l.kind = .col then (u l.flavor : ℂ) else (u l.flavor : ℂ)⁻¹) • point l)

/-- Entrywise complex conjugation on gauge color slots. -/
def cColor : su.Color →L[ℝ] su.Color := LinearMap.toContinuousLinearMap
  (su.projectColor.comp
    ((show Mat →ₗ[ℝ] Mat from
      { toFun := fun A => A.map star
        map_add' := Matrix.map_add star (fun a b => star_add a b)
        map_smul' := fun z A => Matrix.map_smul star z (fun a => by rw [star_smul, star_trivial]) A }).comp su.colorMat))

def turnC (j : ℕ) : Module.End ℝ (Labels.Taylor su j) where
  toFun v := ⟨fun i => cColor.compContinuousMultilinearMap (v.val i), by
    refine ⟨fun i x s => congr_arg cColor (v.property.1 i x s), fun z => ?_⟩
    change ∑ i : Axis, z i • cColor (Tensor.diagonal (v.val i) z) = 0
    rw [← map_zero cColor, ← v.radial_value z, map_sum]
    simp only [map_smul]
    rfl⟩
  map_add' v w := by
    apply Subtype.ext; funext i; ext1
    exact map_add cColor _ _
  map_smul' z v := by
    apply Subtype.ext; funext i; ext1
    exact map_smul cColor z _

def Cmat := gamma 0 * gamma 2

def charge : Pol →ₐ[ℂ] Pol := Algebra.TensorProduct.map (Labels.changed turnC)
  (spinMap fun l => ∑ i : Pinor,
    if l.kind = .col then Cmat l.spin i • point { l with kind := .row, spin := i }
    else - ((Cmat⁻¹) i l.spin) • point { l with kind := .col, spin := i })

/-- Conjugate **coefficients**, preserving order of spin generators. -/
def conjugate (v : Pol) : Pol := (monomial.repr v).sum fun i c => (star c) • (monomial i)

def five (v : Pol) : Pol := (Algebra.TensorProduct.map (AlgHom.id ℂ Bos)
  (spinMap fun l => ∑ i : Pinor,
    if l.kind = .col then g5 i l.spin • point { l with spin := i, kind := .row }
    else -(g5 l.spin i) • point { l with spin := i, kind := .col })) (conjugate v)

def atPol (g : Bos) : Pol := g ⊗ₜ[ℂ] (1:GrassJet)

def slot (x : Letter) : Pol := (1:Bos) ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ (point x)

def unbarred (i : Flav) (s : Pinor) (k : Hue) : Pol := slot ⟨.col,i,s,k,0⟩
def barred   (i : Flav) (s : Pinor) (k : Hue) : Pol := slot ⟨.row,i,s,k,0⟩

def bilinear (i j : Flav) (S : Spike) : Pol :=
  ∑ s, ∑ t, ∑ k, S s t • (barred i s k * unbarred j t k)

/-- Epsilon-color odd, spin order zero, used with distinct flavors. -/
def baryon (i j k : Flav) (s t u : Pinor) : Pol :=
  ∑ p : Equiv.Perm Hue, (Equiv.Perm.sign p).val •
    (unbarred i s (p 0) * unbarred j t (p 1) * unbarred k u (p 2))

/-- Derivative order 0 curvature. Position-degree one connection is a
*Taylor coefficient* also in YM, so no factorial here either. -/
def curvature (i j : Axis) (c : su.ColorIndex) : Bos :=
  ∑ k : Fin (Labels.dim su 0),
    let T := (Labels.axes su 0) k
    C (σ:=Labels.Key su) (((T.value j (YM.basis i) - T.value i (YM.basis j)) c : ℝ) : ℂ) * X ⟨0,k⟩

def tg (i j : Axis) : Pol :=
  atPol ((∑ b, ∑ c, curvature i b c * curvature j b c) -
    if i = j then (4:ℂ)⁻¹ • (∑ a, ∑ b, ∑ c, curvature a b c ^ 2) else 0)

def halfquark (l : Flav) (i j : Axis) : Pol :=
  ∑ s, ∑ t, ∑ k, gamma i s t •
    (barred l s k * slot ⟨.col,l,t,k,Finsupp.single j 1⟩ -
    slot ⟨.row,l,s,k,Finsupp.single j 1⟩ * unbarred l t k)

def tf (l : Flav) (i j : Axis) : Pol := halfquark l i j + halfquark l j i

/-- Leading short-distance **direction and scale** of the physical stress in
comparison frames. Sign for the translation-shell action. -/
def wickStress (i j : Axis) : Pol := -(tg i j) - (4:ℂ)⁻¹ • ∑ l : Fin 6, tf l i j

end Jet
end YM.TorusPCAC
