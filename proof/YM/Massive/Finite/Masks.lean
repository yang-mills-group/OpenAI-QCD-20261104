import YM.Massive.Finite.Core
import YM.QCD.RP.Floor

/-!
# Masked mass exponent and symmetry/support facts on real flavored insertions

Works for any real flavor masses. Sums over sites so that the mass term can
be used as a reflection-square *operator* in the **degenerate** RP theorem,
not using degenerate results about signs of the weight as a gauge marginal.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Onsite
open QCD QCD.Lat QCD.Grass QCD.RP Lattice Wilson Finset NormedSpace Function
open scoped BigOperators Topology Matrix.Norms.Frobenius Matrix ComplexOrder

variable {n : Side} {F : ℕ} (u : Flavor F → ℝ) (X : Support n)

def modes (X : Support n) (F : ℕ) := univ.filter fun i : Modes n F => i.1.1 ∈ X

def offset : Matrix (Modes n F) (Modes n F) ℂ := Matrix.diagonal fun i =>
  if i ∈ modes X F then (u i.2 : ℂ) else 0

@[simp] lemma mem_modes (i : Modes n F) : i ∈ modes X F ↔ i.1.1 ∈ X := by simp [modes]

theorem unmasked (R : Regulator n F) (U : Grid n) :
    R.D U = Lat.copies F (bareD R.t U 0) + offset R.m (univ : Support n) := by
  classical
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases he : i=j <;> by_cases h : a=b <;>
    simp [Regulator.D,copies,bareD, Matrix.blockDiagonal_apply,offset,he,h]
  exact add_comm ..

theorem expansion : form (offset u X) = ∑ i ∈ modes X F, (u i.2 : ℂ) • pair i := by
  classical
  simp [form, offset, Matrix.diagonal_apply, ite_smul, modes, sum_filter, pair]

@[simp] theorem offset_star : star (offset u X)=offset u X := by
  unfold offset
  rw [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]; ext i j
  simp [Matrix.diagonal_apply, apply_ite star]

lemma rotated (k : Frame n) : offset u X*rotates F k=rotates F k*offset u X := by
  ext ⟨⟨i,a⟩,p⟩ ⟨⟨j,b⟩,q⟩
  unfold offset; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : i=j <;> by_cases he : p=q <;>
    simp [rotates,copies,Matrix.blockDiagonal_apply,h,he,siteRot,rides,mul_comm]

theorem invariant (k : Frame n) : slots F k (form (offset u X))=form (offset u X) := by
  rw [slots,form_map,Matrix.transpose_transpose, rotated, ← mul_assoc, (rotates_law F k).1,one_mul]

variable (C : Cells.Cut n)

def opposite (C : Cells.Cut n) (X : Support n) : Support n := X.image C.reflect

@[simp] lemma mem_opposite (i : Site n) : i ∈ opposite C X ↔ C.reflect i ∈ X := by
  classical
  rw [opposite, mem_image]
  constructor
  · rintro ⟨j,h,rfl⟩; simpa
  intro h; exact ⟨C.reflect i,h,C.twice i⟩

lemma folded : folds C F * offset u X = offset u (opposite C X) * folds C F := by
  ext ⟨⟨i,a⟩,p⟩ ⟨⟨j,b⟩,q⟩
  unfold offset; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : C.reflect i=j <;> by_cases he : p=q <;>
    simp [folds,copies,Matrix.blockDiagonal_apply,h,he,rides,mul_comm]

@[simp] lemma reflected : theta C (form (offset u X))=form (offset u (opposite C X)) := by
  rw [theta,tilt_form,offset_star,← mul_assoc,folded,mul_assoc,folds_sq,mul_one]

lemma taped (T : Tape n) : T.tape F (form (offset u X))=form (offset u X) := by
  have he : offset u X*T.bands F = T.bands F*offset u X := by
    ext i j; unfold Tape.bands offset; simp only [Matrix.diagonal_mul_diagonal]; simp [Matrix.diagonal_apply,mul_comm]
  rw [Tape.tape, form_map, Tape.band_trans, he, ← mul_assoc, T.band_sq F,one_mul]

/-- Constant *on links*; actually contains Grassmann variables. -/
def patch : Insertion n F := ContinuousMap.const _ (gauss (offset u X))

lemma patch_invariant : Lat.Invariant (patch u X) := by
  intro k; ext1 U; change slots F k (exp _) = exp _; rw [map_weight,invariant]

lemma plus (U) : Grass.Plus (patch u X U) := gauss_plus _

lemma central (f : Insertion n F) : f*patch u X=patch u X*f := by
  ext1 i; exact (plus u X i).central _

lemma reflected_patch {P : Cut n F} : RP.picture C P (patch u X) = patch u (opposite C X) := by
  unfold picture
  let t := mount C P
  have he (Y : Support n) : t.roll (patch u Y)=patch u Y := by
    ext1 i; change t.tape F (exp _) = exp _; rw [map_weight,taped]
  rw [he]; have h : reflect C (patch u X)=patch u (opposite C X) := by
    ext1 i; change tilt _ (exp _) = exp _; rw [tilt_exp (folds C F)]; congr 1; exact reflected u X C
  rw [h,he]

variable {X}

set_option maxHeartbeats 800000 in
lemma reachable {S : Set (Site n)} (h : (X : Set (Site n)) ⊆ S) :
    form (offset u X) ∈ (pass (setDay (F:=F) S)).range := by
  classical
  rw [expansion]; apply Subalgebra.sum_mem; intro i he
  apply Subalgebra.smul_mem; let j : Deck S F := ((⟨i.1.1,h ((mem_modes ..).mp he)⟩,i.1.2),i.2)
  have hj : setDay S j = i := rfl
  exact ⟨pair j,(pass_pair (setDay (F:=F) S) j).trans (by rw [hj])⟩

lemma floors {S : Set (Site n)} (h : (X : Set (Site n)) ⊆ S) : Floors S (patch u X) := by
  classical
  obtain ⟨k,hk⟩ := reachable u h
  refine ⟨fun _ => exp k,continuous_const,fun _ _ _ => rfl,fun U => ?_⟩
  change exp _ = _; rw [map_weight]; exact congr_arg exp (show pass (setDay (F:=F) S) k = _ from hk).symm

end YM.Massive.Onsite
