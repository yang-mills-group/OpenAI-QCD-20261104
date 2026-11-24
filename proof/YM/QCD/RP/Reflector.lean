import YM.QCD.RP.House

/-! # Hermitian reflection symmetry of the complex weight, no gauge-fix -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lat Lattice Grass Wilson Slice Function Finset NormedSpace MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology
variable {n : Side} {F : ℕ} {C : Lat.Cut n F} {R : Cells.Cut n}
local notation "v" => R.pos
local notation "φ" => plane v
local notation "I" => R.pullC su

private lemma turns_level (U : Grid n) (t : Per n) : theta R (levelTerm C (I U) R t) = levelTerm C U R (level R t) := by
  obtain ⟨V,rfl⟩ := (slice R.pos).symm.surjective U
  change theta R (levelTerm C (I (chain v V)) R t)=levelTerm C (chain v V) R _
  unfold levelTerm hopTerm
  simp_rw [map_sum,map_add,map_sum,theta_bank,fun a : Flat v => tang_span (F:=F) R a.property,Slice.shift,image_plane]
  have he (x : Slice.Row v n) (a : Flat v) : thread C.t (I (chain v V)) a.val (φ t x)=thread C.t (chain v V) a (φ (level R t) x) := by
    simp only [thread, mirrors,chain_space]
    simp only [opposite, Lat.seam,plane_row]
  simp_rw [he]
private lemma turns_slope (h : R.kind=.link) (T : Matches C R) (U : Grid n) (t : Per n) :
    theta R (slope C (I U) R t)=slope C U R (imageChord R t) := by
  obtain ⟨V,rfl⟩ := (slice R.pos).symm.surjective U
  change theta R (slope C (I (chain v V)) R t)=slope C (chain v V) R _
  unfold slope hopTerm
  have hx (x : Slice.Row v n) : Lat.seam C.t (φ t x) v=Lat.seam C.t (φ (imageChord R t) x) v := by
    simp only [Lat.seam,(show C.t v=_ from T),plane_pos,add_left_inj]
    have hl : Involutive (imageChord R) := chord_turn R
    simp only [show imageChord R t=Link.top R ↔ t=Link.top R from by
      nth_rw 1 [← Link.tr h]; exact hl.injective.eq_iff]
  have he (x : Slice.Row v n) : star (thread C.t (I (chain v V)) v (φ t x)) = thread C.t (chain v V) v (φ (imageChord R t) x) := by
    simp only [thread, mirrors,chain_time,hx,star_smul,seam_real,opposite, Pi.inv_apply,colour_inv,star_star,imageChord]
  simp_rw [map_sum,chord_span,he,lift_time,image_plane,chord_end,imageChord,sub_add_cancel]

lemma turns_action (h : R.kind=.link) (T : Matches C R) (U : Grid n) : theta R (C.insertD (I U))=C.insertD U := by
  rw [Lat.Cut.insertD_apply,Lat.Cut.insertD_apply]; unfold gauss
  rw [show theta R (exp (form (C.ferm (I U))))=exp (theta R (form (C.ferm (I U)))) from tilt_exp ..]
  congr 1
  rw [main_calendar (R:=R) C,main_calendar (R:=R) C]; simp_rw [map_add,map_sum,turns_level,turns_slope h T]
  exact congrArg₂ (·+·) (Equiv.sum_comp (Involutive.toPerm _ (level_twice R)) _) (Equiv.sum_comp (Involutive.toPerm _ (chord_turn R)) _)

lemma turns_rate (h : R.kind=.link) (T : Matches C R) (x : Insertion n F) (U : Grid n) :
    C.rate (RP.reflect R x) U=star (C.rate x (I U)) := by
  have hv : Grass.Plus (C.insertD U) := gauss_plus _
  have he : theta R ((C.insertD*x) (I U)) = (C.insertD * RP.reflect R x) U := by simp only [ContinuousMap.mul_apply, theta_mul, reflects, turns_action h T]; exact hv.central _
  rw [Lat.Cut.rate,Lat.Cut.rate, ← he,theta, tilt_amp _ (folds_sq ..), show bare C.β (I U)=_ from bare_pull ..]; simp [mul_comm]

lemma average_turn (h : R.kind=.link) (T : Matches C R) (x : Insertion n F) :
    C.average (RP.reflect R x)=star (C.average x) := by
  have he : C.raw (RP.reflect R x)=star (C.raw x) := by
    change (∫ U, C.rate _ U ∂prior su n)=star (∫ U, C.rate x U ∂prior su n)
    simp_rw [turns_rate h T]
    have hv := prior_pull (G:=su) R.flip R.slide
    have hs : Continuous fun U => star (C.rate x U) := by fun_prop
    have hu := integral_map hv.aemeasurable (by rw [hv.map_eq]; exact hs.aestronglyMeasurable)
    rw [hv.map_eq] at hu; exact hu.symm.trans (integral_conj ..)
  simp only [Lat.Cut.average,LinearMap.smul_apply,he]; simp
end YM.QCD.RP
