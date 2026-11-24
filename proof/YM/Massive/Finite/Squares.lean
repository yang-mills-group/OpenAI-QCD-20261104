import YM.Massive.Finite.Masks

/-!
# Reflection positivity on the full joint regulated theory, unequal real masses

All continuous gauge-invariant sided insertions including parity-odd, all link planes
incl those crossing seam(s) on the torus, any flavor number, any real bare masses.
Raw and normalized result distinguished.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass Lattice Wilson MeasureTheory Function
open scoped BigOperators Topology Matrix.Norms.Frobenius ComplexOrder

variable {n : Side} {F : ℕ} (R : Regulator n F)

namespace Regulator

/-- auxiliary Cut; degrees of freedom & kernel conventions unchanged -/
def zeroCut : Lat.Cut n F := ⟨R.β,R.t,0⟩

theorem compareDensity : R.density=(common R.zeroCut).density * Onsite.patch R.m Finset.univ := by
  ext1 U
  rw [ContinuousMap.mul_apply,density_apply,density_apply,Onsite.unmasked,gauss_add,smul_mul_assoc]; rfl

theorem asCut (x : Lat.Insertion n F) : R.raw x=R.zeroCut.raw (Onsite.patch R.m Finset.univ*x) := by
  rw [← common_raw]; change joint ⇑(R.density*x)=joint _; rw [compareDensity,mul_assoc]

variable {R}
open QCD.RP
variable {C : Cells.Cut n} (h : C.kind=.link) (hβ : 0 ≤ R.β) (hl : 2 ≤ C.half.val)

include h hl in
lemma viaCut (K : Lat.Cut n F) (hk : 0 ≤ K.β) (x : Insertion n F) (hx : Floors C.sector x)
    (hv : Invariant x) : 0 ≤ K.raw (picture C K x*x) := by
  rw [← Tape.roll_raw (mount C K) K (show (mount C K).start = _ from rfl),Tape.roll_mul,picture,Tape.unroll]
  exact RP.raw_positive h (tuned C K) hl hk _ ((sided _).mp (rolling_maps _ hx)) ((mount C K).roll_invariant _ hv)

include h
open Onsite

lemma squares (R : Regulator n F) {X : Support n} (hx : (X : Set _)=C.sector) :
    patch R.m (Finset.univ : Support n) = picture C R.zeroCut (patch R.m X)*patch R.m X := by
  rw [reflected_patch]
  ext1 U; rw [ContinuousMap.mul_apply]; change gauss _=gauss _*gauss _
  rw [← gauss_add]; congr 1
  ext i j; by_cases hh : i=j
  · subst j; have ht : ∀ x, x ∈ X ↔ x ∈ C.sector := by rw [← hx]; intro x; rfl
    by_cases he : i.1.1 ∈ C.sector
    · simp [offset,ht, he, C.link_switch h he]
    simp [offset,ht,he,(RP.switch C h _).mp he]
  simp [offset,hh]

include hl hβ
lemma raw_reflection (x : Lat.Insertion n F) (hx : Floors C.sector x)
    (hv : Invariant x) : 0 ≤ R.raw (picture C R.zeroCut x*x) := by
  classical
  let X := Finset.univ.filter fun i : Site n => i ∈ C.sector
  have hX : (X : Set _)=C.sector := by ext; simp [X]
  let p : Insertion n F := patch R.m X
  let q := picture C R.zeroCut x
  rw [R.asCut, squares h R hX]
  have hk : picture C R.zeroCut (x*p)*(x*p)=picture C R.zeroCut p*p*(q*x) := by
    rw [pic_mul]
    change picture C R.zeroCut p*q*(x*p) = _
    rw [← mul_assoc _ x p, mul_assoc _ q x, mul_assoc, central, ← mul_assoc]
  change 0 ≤ R.zeroCut.raw (picture C R.zeroCut p*p*(q*x)); rw [← hk]
  exact viaCut h hl R.zeroCut hβ _ (flooring_mul hx (floors _ hX.le)) (invariant_mul _ _ hv (patch_invariant R.m X))

lemma average_reflection (hz : 0 < R.Z) (x : Lat.Insertion n F) (hx : Floors C.sector x)
    (hv : Invariant x) : 0 ≤ R.average (picture C R.zeroCut x*x) :=
  mul_nonneg (inv_nonneg.mpr hz.le) (raw_reflection h hβ hl x hx hv)

lemma Z_nonneg : 0 ≤ R.Z := by
  simpa only [Z,pic_one,mul_one] using raw_reflection h hβ hl 1 flooring_one invariant_one

omit hl hβ h in
-- as in RP/Floor (use both real & imaginary tests in complex order)
private lemma hermitian (a b z w : ℂ) (A : 0 ≤ a) (B : 0 ≤ b)
    (H : ∀ c : ℂ, 0 ≤ a+c*z+star c*w+c*star c*b) : star z=w := by
  have hr := Complex.nonneg_iff.mp (H 1)
  have hi := Complex.nonneg_iff.mp (H Complex.I)
  rw [Complex.nonneg_iff] at A B
  simp [Complex.mul_im, ← A.2, ← B.2] at hr hi
  apply Complex.ext <;> simp
  all_goals linarith

/-- Supplied project's complex form estimate instantiated on the true raw expectation.
No hypothesis on normalization. -/
theorem schwarz (x y : Insertion n F) (hx : Floors C.sector x) (hy : Floors C.sector y)
    (H : Invariant x) (K : Invariant y) :
    let L := fun x y : Insertion n F => R.raw (picture C R.zeroCut x*y)
    ‖L x y‖^2 ≤ ‖L x x‖ * ‖L y y‖ := by
  intro L; have ha : 0 ≤ L x x := raw_reflection h hβ hl _ hx H
  have hb : 0 ≤ L y y := raw_reflection h hβ hl _ hy K
  have he (c : ℂ) : 0 ≤ L x x+c*L x y + star c*L y x + c*star c*L y y := by
    have hi : 0 ≤ L (x+c • y) (x+c • y) := raw_reflection h hβ hl _
      (flooring_add hx (flooring_smul _ hy)) (invariant_add _ _ H (invariant_smul _ K _))
    apply hi.trans_eq
    unfold L; rw [pic_add,pic_smul]; simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc,map_add,map_smul, smul_eq_mul]; ring
  apply Cells.schwarz ha hb; intro t
  have hr := he (star t); rw [star_star,mul_comm (star t) t, ← hermitian _ _ _ _ ha hb he] at hr
  exact hr
end Regulator
end YM.Massive
