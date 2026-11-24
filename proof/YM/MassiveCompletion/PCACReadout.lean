import YM.MassiveCompletion.SixFit

/-! Recover six masses from oriented, complex, off-diagonal Ward readouts. The
pseudoscalar normalization may be fixed before the fit. The last theorem allows
different RG depths on successive regulators. -/

set_option autoImplicit false
noncomputable section

namespace YM.Massive.PCAC.Readout
open Filter Finset YM.MassiveCompletion.SixFit
open scoped Topology

abbrev ComplexPairs := Fin 6 → Fin 6 → ℂ

def pairRead (Z : ComplexPairs) : PairMass := fun i j => ((Z i j).re + (Z j i).re) / 2

def estimate (Z : ComplexPairs) : Mass := Squares.average (pairRead Z)

theorem pairRead_symm (Z : ComplexPairs) (i j : Fin 6) : pairRead Z i j = pairRead Z j i := by
  unfold pairRead
  rw [add_comm]

theorem fit_unique (Z : ComplexPairs) (m : Mass) : Fit (pairRead Z) m ↔ m = estimate Z := by
  constructor
  · exact Squares.unique (pairRead Z) m (fun i j _ => pairRead_symm Z i j)
  · rintro rfl
    exact Squares.fit (pairRead Z) (fun i j _ => pairRead_symm Z i j)

/-- Both orientations refer to the same regulator. Imaginary contamination is
allowed; no symmetry of the input data is required. -/
theorem estimate_error {Z : ComplexPairs} {m : Mass} {ε : ℝ}
    (h : ∀ i j, i ≠ j → ‖Z i j - ((m i + m j : ℝ) : ℂ)‖ ≤ ε) (k : Fin 6) :
    |estimate Z k - m k| ≤ 2 * ε := by
  apply Squares.near k (pairRead Z) m ε
  intro i j hij
  have h₁ : |(Z i j).re - (m i + m j)| ≤ ε := by
    simpa using (Complex.abs_re_le_norm _).trans (h i j hij)
  have h₂ : |(Z j i).re - (m i + m j)| ≤ ε := by
    simpa [add_comm (m j) (m i)] using (Complex.abs_re_le_norm _).trans (h j i hij.symm)
  rw [abs_le] at h₁ h₂ ⊢
  unfold pairRead
  constructor <;> linarith

theorem positive_injective {Z : ComplexPairs} {m : Mass} {ε : ℝ}
    (h : ∀ i j, i ≠ j → ‖Z i j - ((m i + m j : ℝ) : ℂ)‖ ≤ ε)
    (hp : ∀ i, 2 * ε < m i) (hs : ∀ i j, i ≠ j → 4 * ε < |m i - m j|) :
    (∀ i, 0 < estimate Z i) ∧ Function.Injective (estimate Z) := by
  have he := fun i => abs_le.mp (estimate_error h i)
  constructor
  · intro i
    linarith [(he i).1, hp i]
  · intro i j hij
    by_contra hn
    have hgap := hs i j hn
    have hle : |m i - m j| ≤ 4 * ε := by
      apply abs_le.mpr
      constructor <;> linarith [(he i).1, (he i).2, (he j).1, (he j).2]
    exact (not_lt_of_ge hle) hgap

/-- A fixed physical denominator can be small on fine regulators. Relative
control suffices and avoids assuming a cutoff-uniform absolute lower bound. -/
theorem relative_ratio {A P c : ℂ} {ε : ℝ} (hP : P ≠ 0)
    (h : ‖A - c * P‖ ≤ ε * ‖P‖) : ‖A / P - c‖ ≤ ε := by
  rw [show A / P - c = (A - c * P) / P by field_simp, norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hP)).mpr h

/-- Primitive increments for a Wilson-breaking comparison telescope along
any finite history. The field, spectator, and normalization are fixed along
that history. No uniform bound on its length is required. -/
theorem accumulate (D : ℕ → ℂ) (cost : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, ‖D (j+1) - D j‖ ≤ cost j) :
    ‖D n‖ ≤ ‖D 0‖ + ∑ j ∈ range n, cost j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hn := ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self _)))
    calc
      ‖D (n+1)‖ = ‖(D (n+1) - D n) + D n‖ := by rw [sub_add_cancel]
      _ ≤ ‖D (n+1) - D n‖ + ‖D n‖ := norm_add_le _ _
      _ ≤ _ := by linarith [h n (Nat.lt_succ_self _)]

/-- The least-squares fit of the ordinary, possibly nonsymmetric Ward ratios
converges to the six reference masses whenever the physical defects close in
units of their respective pseudoscalar denominators, on a common filter. -/
theorem fit_limit_of_relative_defects {κ : Type*} {f : Filter κ} {m : Mass}
    {A P : κ → ComplexPairs} {ε : κ → ℝ}
    (hε : Tendsto ε f (𝓝 0))
    (h : ∀ᶠ q in f, ∀ i j, i ≠ j → P q i j ≠ 0 ∧
      ‖A q i j - ((m i + m j : ℝ) : ℂ) * P q i j‖ ≤ ε q * ‖P q i j‖) :
    Tendsto (fun q => estimate (fun i j => A q i j / P q i j)) f (𝓝 m) := by
  apply tendsto_pi_nhds.mpr
  intro k
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hsmall := (Metric.tendsto_nhds.mp hε) (δ / 2) (half_pos hδ)
  filter_upwards [h, hsmall] with q hq he
  have hfit := estimate_error (m := m) (ε := ε q) (Z := fun i j => A q i j / P q i j)
    (fun i j hij => relative_ratio (hq i j hij).1 (hq i j hij).2) k
  rw [Real.dist_eq] at he ⊢
  simp only [sub_zero] at he
  linarith [le_abs_self (ε q)]

/-- A sufficient microscopic input for the preceding result consists of
primitive bounds on each blocking increment and the normalized sum of their
costs; an identity binds the final defect to the actual measured correlators. -/
theorem fit_limit_of_accumulated_defects {κ : Type*} {f : Filter κ} {m : Mass}
    {A P : κ → ComplexPairs} {n : κ → ℕ} {ε : κ → ℝ}
    {D : κ → Fin 6 → Fin 6 → ℕ → ℂ} {cost : κ → Fin 6 → Fin 6 → ℕ → ℝ}
    (hε : Tendsto ε f (𝓝 0))
    (h : ∀ᶠ q in f, ∀ i j, i ≠ j →
      P q i j ≠ 0 ∧
      D q i j (n q) = A q i j - ((m i + m j : ℝ) : ℂ) * P q i j ∧
      (∀ k < n q, ‖D q i j (k+1) - D q i j k‖ ≤ cost q i j k) ∧
      ‖D q i j 0‖ + ∑ k ∈ range (n q), cost q i j k ≤ ε q * ‖P q i j‖) :
    Tendsto (fun q => estimate (fun i j => A q i j / P q i j)) f (𝓝 m) := by
  apply fit_limit_of_relative_defects hε
  filter_upwards [h] with q hq
  intro i j hij
  obtain ⟨hP, hD, hk, ht⟩ := hq i j hij
  exact ⟨hP, hD ▸ (accumulate (D q i j) (cost q i j) (n q) hk).trans ht⟩

end YM.Massive.PCAC.Readout

#print axioms YM.Massive.PCAC.Readout.fit_limit_of_accumulated_defects
#print axioms YM.Massive.PCAC.Readout.positive_injective
