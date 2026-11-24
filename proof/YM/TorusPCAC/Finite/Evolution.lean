import YM.TorusPCAC.Finite.Step
import YM.TorusPCAC.Finite.CheckerPressure

/-!
# Exact iteration including with a single normalized vacuum

No regularity assumptions on these clock and mass choices in q.
Explicit power factor through all those steps identifies every stage's full
normalization, even for a marked history from arbitrary continuous inputs.
Use positivity here by the bare checker budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.History
open QCD QCD.Lat QCD.Grass Lattice Wilson MeasureTheory Function Filter Finset
open scoped Topology BigOperators Matrix ComplexOrder Matrix.Norms.Frobenius
variable {N : ℕ}
variable (H : History N) (q : ℕ) {m j : ℕ}

lemma usable_step (m) : NormalizedStep (H.step m q) (H.beta q (m+1)) (H.w q m) N :=
    Finite.normalized _ (H.branches m) ..

lemma push_refl (X : Density (H.lattice m q) N) : H.push q m m X=X := by rw [History.push]; simp
@[simp] lemma actual_at : H.actual q (H.depth q)=(H.start q).weight := H.push_refl ..
lemma push_next (X : Density (H.lattice j q) N) (h : m < j) :
    H.push q m j X=block (H.step m q) (H.beta q (m+1)) (H.w q m) (H.push q (m+1) j X) := by
  rw [History.push]; rw [dif_neg h.ne', dif_pos h]
lemma actual_next (h : m < H.depth q) :
    H.actual q m = block (H.step m q) (H.beta q (m+1)) (H.w q m) (H.actual q (m+1)) := H.push_next q _ h

/-- The w⁽²ᴮ⁾ in each step. (Sites here always the *coarser*
ones of the pair.) -/
def factor (m) := (H.w q m)^(2*Fintype.card (Modes (H.lattice m q) N))
def scale (m j : ℕ) := ∏ i ∈ Ico m j, H.factor q i
@[simp] lemma scale_refl (m) : H.scale q m m = 1 := by simp [scale]
lemma scale_next (h : m<j) : H.scale q m j= H.factor q m* H.scale q (m+1) j := by
  unfold scale; rw [← insert_Ico_add_one_left_eq_Ico h, prod_insert]; simp

theorem continuous_push (X : Density (H.lattice j q) N) (hX : Continuous X) (h : m ≤ j) : Continuous (H.push q m j X) := by
  induction h using Nat.decreasingInduction with
  | self => rw [H.push_refl]; exact hX
  | of_succ i hi ih => rw [H.push_next q X hi]; exact Finite.continuous_block _ (H.branches i) _ ih ..

theorem volume_push (X : Density (H.lattice j q) N) (hX : Continuous X) (h : m ≤ j) :
    Density.volume (H.push q m j X) = (H.scale q m j : ℂ) * Density.volume X := by
  induction h using Nat.decreasingInduction with
  | self => rw [H.push_refl,H.scale_refl]; simp
  | of_succ i hi ih =>
    rw [H.push_next q X hi, (H.usable_step q i).2 _ (H.continuous_push q X hX hi) |>.2.2, ih, H.scale_next q hi]
    simp_rw [factor,Complex.ofReal_mul,Complex.ofReal_pow,mul_assoc]

theorem add (X Y : Density (H.lattice j q) N) (hx : Continuous X) (hy : Continuous Y) (h : m ≤ j) :
    H.push q m j (X+Y)=H.push q m j X+H.push q m j Y := by
  induction h using Nat.decreasingInduction with
  | self => simp_rw [push_refl]
  | of_succ i hi ih => simp_rw [H.push_next q _ hi, ih, Finite.block_add (H.step i q) (H.branches i) _ _ _ _
      (H.continuous_push q X hx hi) (H.continuous_push q Y hy hi)]

theorem grade_progress (X : Density (H.lattice j q) N) (hx : Continuous X) (h : m≤j) :
    H.push q m j (fun V=> grade (X V)) = fun V=> grade (H.push q m j X V) := by
  induction h using Nat.decreasingInduction with
  | self => simp_rw [push_refl]
  | of_succ i hi ih => simp_rw [H.push_next q _ hi, ih, Finite.block_grade (H.step i q) (H.branches i) _
      (H.continuous_push q X hx hi)]

lemma actual_cont (h : m ≤ H.depth q) : Continuous (H.actual q m) := H.continuous_push _ _ (Torus.continuous_weight _) h
lemma actual_plus (h : m ≤ H.depth q) (U) : Plus (H.actual q m U) := by
  let X := (H.start q).weight
  have hQ : (fun i=> grade (X i))=X:= funext (H.start q).plus
  have he := H.grade_progress q X (H.start q).continuous_weight h; rw [hQ] at he; exact (congr_fun he U).symm

lemma total (h : m ≤ H.depth q) : Density.volume (H.actual q m)=
    ((H.scale q m (H.depth q) * (H.start q).partition : ℝ):ℂ) := by
  rw [actual,H.volume_push _ _ (H.start q).continuous_weight h,Torus.volume,Complex.ofReal_mul]

lemma scale_pos (hh : ∀ i, m ≤ i → i < j → 0 < H.w q i) : 0 < H.scale q m j := by
  unfold scale; exact prod_pos fun i hi => pow_pos (hh i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2) _

lemma lattice_size (m : ℕ) : 4 ≤ (H.lattice m q).val ∧ Even (H.lattice m q).val := by
  have hx := H.S.side_four m q
  exact ⟨Nat.le_of_dvd (H.lattice m q).property hx, even_iff_two_dvd.mpr (dvd_trans (by decide : 2∣(4:ℕ)) hx)⟩

/-- At any finite size q, no zero even at the coarse stops, supporting the
normalizing divisions for all observables. Reader pressure exponent here is
at `sites (H.UV q)`, cannot be silently specialized to `sites` at m. -/
theorem sea (hb : 0≤H.beta q (H.depth q)) (hv : ∀ i, i<H.depth q → 0<H.w q i)
    (hm : ∀ i, H.mass q i≠-4) (hh : m≤ H.depth q) : 0 < Density.volume (H.actual q m) ∧
      (H.scale q m (H.depth q) * Wilson.partition su (H.UV q) (H.beta q (H.depth q)) *
       (∏ i : Flavor N, ((4:ℝ) + H.mass q i)^12) ^ sites (H.UV q) ≤ (Density.volume (H.actual q m)).re) := by
  rw [H.total q hh]
  have hp:= H.lattice_size q (H.depth q)
  have hS := H.scale_pos q (m:=m) (fun i _ hi=> hv i hi)
  exact ⟨Complex.zero_lt_real.mpr (mul_pos hS (Finite.real_normalization (H.start q) hb hp.2 hp.1 hm)),
    le_trans (le_of_eq (mul_assoc ..)) (mul_le_mul_of_nonneg_left (Finite.bare_comparison (H.start q) hb hp.2 hp.1) hS.le)⟩

/-- Arbitrary continuous density insertion, exact through any number of steps.
No restart of the scalar normalization even if the word itself has odd fields. -/
theorem word (hb : 0≤H.beta q (H.depth q)) (hv : ∀ i, i<H.depth q → 0<H.w q i)
    (hm : ∀ i, H.mass q i≠-4) (hh : m≤ H.depth q) (X : Density (H.UV q) N) (hX : Continuous X) :
    Density.volume (H.push q m (H.depth q) ((H.start q).weight * X)) / Density.volume (H.actual q m) =
    Density.normalize (H.actual q (H.depth q)) X := by
  have hw: Continuous (H.start q).weight:= (H.start q).continuous_weight
  unfold Density.normalize Density.moment; rw [H.volume_push q _ (hw.mul hX) hh,H.total q hh,
    Complex.ofReal_mul,H.actual_at,Torus.volume]
  have he:= (H.sea q hb hv hm hh).1.ne'; rw [H.total q hh,Complex.ofReal_mul] at he
  field_simp [left_ne_zero_of_mul he,right_ne_zero_of_mul he]
end YM.TorusPCAC.History
#print axioms YM.TorusPCAC.History.word
