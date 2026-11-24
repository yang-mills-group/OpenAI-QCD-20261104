import YM.Euclid.Register
/-! Outer calculus with general finite-dimensional letters with discrete rotation and reality.
Variant of Euclid/Register & following Next/ROTATIONS atmospheric code.
Does not invoke analytic data/expense from an auxiliary gauge theory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Spiral
open Labels
open scoped Topology BigOperators
structure Register (G : Gauge) where
  (size : ℕ→ ℕ)
  scalar (d:ℕ): Fin (size d) → ℂ
  mirrorGroup (d:ℕ)(s:Signed) : (Fin (size d) → ℂ)→ₗ[ℂ](Fin (size d) → ℂ)
  mirror_scalar(s:Signed)(d): mirrorGroup d s (scalar d)= scalar d
  mirror_mul (s q : Signed) (d : ℕ) (v : Fin (size d)→ℂ) :
    mirrorGroup d (s*q) v = mirrorGroup d s (mirrorGroup d q v)
  mirror_one (d : ℕ) (v : Fin (size d) →ℂ) : mirrorGroup d 1 v = v
  star_mirror (s : Signed) (d : ℕ) (v : Fin (size d)→ℂ) :
    star (mirrorGroup d s v) = mirrorGroup d s (star v)
  bar_scalar (d : ℕ) : star (scalar d)=scalar d
namespace Register
variable {G: Gauge}(L:Register G)
abbrev Ref (d:ℕ):= Fin (L.size d)→ℂ
def bar (d:ℕ): L.Ref d →ₛₗ[starRingEnd ℂ] L.Ref d where
  toFun p:= star p
  map_add' p q := star_add p q
  map_smul' r p := star_smul r p
@[simp] theorem bar_apply (d) (x : L.Ref d) : L.bar d x = star x := rfl
attribute [simp] mirror_scalar mirror_mul mirror_one star_mirror bar_scalar
/-- Reflection adjoint at coordinate through 0. Use `bar` alone for ordinary complexification, Euclidean real label conventions. -/
def adj (d : ℕ) (a : Axis) : L.Ref d →ₛₗ[starRingEnd ℂ] L.Ref d :=
  (L.mirrorGroup d (Signed.mirror a)).comp (L.bar d)

@[simp] theorem adj_scalar (d a) : L.adj d a (L.scalar d) = L.scalar d := by
  simp only [adj,LinearMap.comp_apply,bar_apply,bar_scalar,mirror_scalar]

@[simp] theorem reflected (d a) (v : L.Ref d) : L.adj d a (L.adj d a v) = v := by
  simp only [adj,LinearMap.comp_apply,bar_apply,star_mirror, star_star]
  rw [← mirror_mul, show Signed.mirror a * Signed.mirror a = 1 from
    calc
      _ = (Signed.mirror a)⁻¹ * Signed.mirror a := rfl
      _ = _ := inv_mul_cancel _, mirror_one]

/-- Reference label carrying its own weight. Works across arities with no casts
until reading a slot. -/
abbrev Token := (d : ℕ) × L.Ref d

def one (d : ℕ) : L.Token := ⟨d,L.scalar d⟩
def move (s : Signed) (x : L.Token) : L.Token := ⟨x.1,L.mirrorGroup x.1 s x.2⟩
def conjugate (x : L.Token) : L.Token := ⟨x.1,star x.2⟩
def reflectedToken (a : Axis) (x : L.Token) : L.Token := ⟨x.1,L.adj x.1 a x.2⟩

@[simp] theorem token_adjoint (a : Axis) (x : L.Token) : L.move (Signed.mirror a) (L.conjugate x) = L.reflectedToken a x := rfl
end Register
end YM.Spiral

#print axioms YM.Spiral.Register.reflected
