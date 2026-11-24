import YM.TorusPCAC.Finite.Reflection

/-!
# Marker insertion and half-wall bill

Strengthen the proofs of positivity to an inequality across the reflected
link plane. Work *before* any normalizations, on actual densities,
using the §massread/projector gamma matrices. Give particularly useful
formulas for reading mass markers in these bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Finite
open QCD QCD.Lat Lattice Wilson QCD.RP NormedSpace MeasureTheory Function Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Matrix ComplexOrder Classical
variable {n : Side} {N : ℕ}

namespace Link

/-- Orthogonality check for mixed forms at a fixed seam, independent of
`B.partition`. Cf. `RP.sch`, proof of the corresponding normalized
inequality for flavor degeneracy. -/
private lemma conjugates (a b z w : ℂ) (A : 0 ≤ a) (B : 0 ≤ b)
    (H : ∀ c : ℂ, 0 ≤ a+c*z+star c*w+c*star c*b) : star z=w := by
  have hr := Complex.nonneg_iff.mp (H 1)
  have hi := Complex.nonneg_iff.mp (H Complex.I)
  rw [Complex.nonneg_iff] at A B
  simp [Complex.mul_im, ← A.2, ← B.2] at hr hi
  apply Complex.ext <;> simp <;> linarith

theorem reflect_cs (R : Cells.Cut n) (h : R.kind=.link) (B : Torus n N) (hb : 0≤B.beta)
    (hL : 2≤R.half.val) (x y : Insertion n N) (X : Floors R.sector x) (Y : Floors R.sector y)
    (H : Invariant x) (K : Invariant y) :
    let L (x y : Insertion n N) := Density.moment B.weight (picture R B.starter x*y : Insertion n N)
    ‖L x y‖^2 ≤ ‖L x x‖ * ‖L y y‖ := by
  intro L
  have ha := show 0 ≤ L x x from raw_positive_mass R B x h hb hL H X
  have hb' := show 0 ≤ L y y from raw_positive_mass R B y h hb hL K Y
  have he (c : ℂ) : 0 ≤ L x x+c*L x y+star c*L y x+c*star c*L y y := by
    have hh : 0 ≤ L (x+c • y) (x+c • y) := raw_positive_mass R B _ h hb hL
      (invariant_add _ _ H (invariant_smul _ K c)) (flooring_add X (flooring_smul c Y))
    apply hh.trans_eq; unfold L; simp_rw [Torus.moment_eq]; rw [pic_add,pic_smul]
    simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc,map_add,map_smul,smul_eq_mul]; ring
  apply Cells.schwarz ha hb'; intro t
  have hr := he (star t); rw [star_star] at hr
  have hv := conjugates (L x x) (L y y) (L x y) (L y x) ha hb' he
  rw [mul_comm (star t) t,← hv] at hr; exact hr
end Link

namespace Marker
open Slab

/-- Site assignment, measured by Grassmann raw bilinear. -/
def matrix (n : Side) (N : ℕ) (F : Site n → ℝ) : Matrix (Modes n N) (Modes n N) ℂ :=
  Matrix.diagonal fun i => ↑(F i.1.1)

def probe (F : Site n → ℝ) : Insertion n N := ContinuousMap.const _ (Grass.gauss (matrix n N F))

def unitT (n : Side) (N : ℕ) : Torus n N := ⟨0,0, fun _=>1⟩

lemma toSlab (n : Side) (N : ℕ) (F : Site n → ℝ) : matrix n N F=Slab.assign (unitT n N) F := by simp [matrix,Slab.assign,unitT]

lemma form (F : Site n → ℝ) : Grass.form (matrix n N F)=∑ i : Site n, (F i:ℂ) • atoms (unitT n N) i := by rw [toSlab,form_assign]
@[simp] lemma probe_apply (F : Site n → ℝ) (U : Grid n) : (probe (N:=N) F U : Fields n N)=Grass.gauss (matrix n N F) := rfl

lemma adds (F G : Site n → ℝ) : probe (N:=N) (F+G)=probe F * probe G := by
  ext1 U; simp_rw [ContinuousMap.mul_apply,probe_apply,toSlab,Slab.assign_add,Grass.gauss_add]

lemma commute (F G : Site n → ℝ) : Commute (probe (N:=N) F) (probe G) := by
  show probe (N:=N) F * _ = _; rw [← adds, add_comm, adds]

lemma rotated (F : Site n → ℝ) : Invariant (probe (N:=N) F) := by
  intro k; ext1 U
  change slots N k (Grass.gauss (matrix n N F))=Grass.gauss _
  rw [slots,Grass.gauss_map,Matrix.transpose_transpose,toSlab, (commute_assign (unitT n N) F k).eq,
    ← Matrix.mul_assoc, (rotates_law N k).1, one_mul]

lemma flips (R : Cells.Cut n) (F : Site n → ℝ) (C : Lat.Cut n N) :
    picture R C (probe F)=probe (F ∘ R.reflect) := by
  ext1 U; rw [picture,Tape.rolls,reflects,Tape.rolls,probe_apply,probe_apply];
  simp_rw [toSlab,tape_gauss,Slab.theta,tape_gauss]

lemma lies (R : Cells.Cut n) (F : Site n → ℝ) (h : support F ⊆ R.sector) : Floors R.sector (probe (N:=N) F) := by
  rw [RP.sided]
  let g := ∑ x : Sky R, ∑ i : Wind N,
    (F x.val:ℂ) • (Grass.psi (place x i)*Grass.bar (place x i))
  refine ⟨fun _=>exp g,continuous_const,(fun _ _ _=>rfl),fun _=>?_⟩; rw [probe_apply,Grass.gauss, form, Grass.map_weight]; congr 1
  let B:=unitT n N
  have he : Grass.pass (light R) g=∑ x : Sky R, (F x.val:ℂ) • atoms B x.val := by
    unfold atoms g
    simp_rw [map_sum,map_smul,map_mul,Grass.pass_psi,Grass.pass_bar, smul_sum, show ∀ i, B.mass i=1 from fun _=>rfl, Complex.ofReal_one,one_smul]; rfl
  rw [he,← sum_subtype (univ.filter fun x=>x∈R.sector) (by simp) (fun x:Site n=> (F x:ℂ) • atoms B x), sum_filter]
  apply sum_congr rfl; intro i _; split_ifs with hh; · rfl
  simp only [show F i=0 from not_not.mp (mt (@h i) hh),Complex.ofReal_zero, zero_smul]

variable (B : Torus n N)
def price (F : Site n → ℝ) := ‖Density.moment B.weight (probe (N:=N) F)‖

lemma split (R : Cells.Cut n) (F G : Site n → ℝ) (h : R.kind=.link)
   (hb : 0 ≤ B.beta) (he : 2 ≤ R.half.val) (hf : support F ⊆ R.sector) (hg : support G ⊆ R.sector) :
    price B (F + G ∘ R.reflect)^2 ≤ price B (F+F∘R.reflect) * price B (G+G∘R.reflect) := by
  have hk := Link.reflect_cs R h B hb he (probe G) (probe F) (lies R G hg) (lies R F hf) (rotated G) (rotated F)
  dsimp only at hk
  simp_rw [flips,← adds] at hk; rw [add_comm _ F,add_comm _ G,
    add_comm (F∘ R.reflect) F] at hk
  unfold price; rw [mul_comm]; exact hk
end Marker
end YM.TorusPCAC.Finite
