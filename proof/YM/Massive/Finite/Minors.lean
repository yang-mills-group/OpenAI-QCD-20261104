import YM.Massive.Finite.Saturate

/-!
# Evaluate Berezin on a partially saturated Grassmann Gaussian

No inverse Dirac matrices; delete rows/columns hit by the insertion.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Saturate
open QCD QCD.Lat QCD.Grass QCD.RP Finset Lattice Wilson MeasureTheory Function NormedSpace
open scoped BigOperators Topology Matrix.Norms.Frobenius

variable {A : Type*} [Fintype A]
variable {X : Finset A} {a : A}

lemma psi_vol (h : a ∈ X) : psi a * vol X = 0 := by
  classical
  rw [← insert_erase h, vol_step (X.erase a) a (notMem_erase a X),pair, ← mul_assoc, ← mul_assoc,psi,atom_square,zero_mul,zero_mul]
lemma bar_vol (h : a ∈ X) : bar a * vol X = 0 := by
  classical
  rw [← insert_erase h, vol_step (X.erase a) a (notMem_erase a X),pair,
    atom_flip (Sum.inl a : Pairs A) (Sum.inr a), ← mul_assoc, mul_neg, ← mul_assoc,atom_square,zero_mul,neg_zero,zero_mul]

lemma blocks {i j : A} (h : j ∈ X) : psi j * bar i * vol X = 0 := by
  rw [atom_flip (Sum.inl j : Pairs A) (Sum.inr i), neg_mul,mul_assoc]; change -(_ * (psi j * vol X)) = _
  rw [psi_vol h,mul_zero,neg_zero]

lemma matched_power (x y v : Dirac A) (h : x*v=y*v) (hp : Grass.Plus v) (n : ℕ) : x^n*v=y^n*v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',pow_succ,mul_assoc,ih,(hp.central _).eq, ← mul_assoc,h,(hp.central _).eq,mul_assoc]
                 rw [← pow_succ' y, ← pow_succ y, ← (hp.central _).eq]

lemma matched_exp (x y v : Dirac A) (h : x*v=y*v) (hp : Grass.Plus v) :
    exp x*v=exp y*v := by
  let f (p : Dirac A) (n : ℕ) := (n.factorial:ℂ)⁻¹ • p^n
  have he (p : Dirac A) : HasSum (fun i => f p i*v) (exp p*v) := (exp_series_hasSum_exp' p (𝕂:=ℂ)).mul_right _
  apply HasSum.unique _ (he y)
  rw [show (fun i => f y i*v)=(fun i => f x i*v) by
      funext i; unfold f; rw [smul_mul_assoc,smul_mul_assoc,matched_power x y v h hp]]
  exact he x

variable [DecidableEq A]

def minor (D : Matrix A A ℂ) (X : Finset A) : Matrix ↥Xᶜ ↥Xᶜ ℂ := D.submatrix Subtype.val Subtype.val

lemma restricted (D : Matrix A A ℂ) :
    form D * vol X = pass (fun i : ↥Xᶜ => i.val) (form (minor D X)) * vol X := by
  let f (i j : A) := (D i j • (psi j * bar i)) * vol X
  unfold form
  simp only [map_sum,sum_mul,map_mul, map_smul, pass_psi,pass_bar]
  change ∑ i : A, ∑ j : A, f i j = ∑ i : ↥Xᶜ, ∑ j : ↥Xᶜ, f i j
  simp_rw [sum_coe_sort]
  rw [sum_coe_sort Xᶜ (fun i:A => ∑ j ∈ Xᶜ, f i j)]
  rw [← sum_subset (subset_univ Xᶜ) _]
  · apply sum_congr rfl; intro i _; apply Eq.symm
    refine sum_subset (subset_univ Xᶜ) ?_
    intro l _ h; unfold f; rw [smul_mul_assoc,blocks (by simpa using h), smul_zero]
  intro l _ h; apply sum_eq_zero; intro i _; unfold f; rw [smul_mul_assoc,mul_assoc,bar_vol (by simpa using h),mul_zero,smul_zero]

theorem minor_value (D : Matrix A A ℂ) (X : Finset A) : ber A (gauss D * vol X) = (minor D X).det := by
  rw [gauss, matched_exp _ _ _ (restricted D) (vol_plus _), ← map_weight (pass _)]
  let s : ↥X ↪ A := Embedding.subtype _
  let t : ↥Xᶜ ↪ A := Embedding.subtype _
  have hu : Bijective (Sum.elim (⇑t) (⇑s)) := by
    constructor
    · rintro (i|i) (j|j) h
      · rw [show i=j from t.injective h]
      · have hj : i.val=j.val:= h; exact (mem_compl.mp i.property (hj.symm ▸ j.property)).elim
      · have hj : i.val=j.val:= h; exact (mem_compl.mp j.property (hj ▸ i.property)).elim
      rw [show i=j from s.injective h]
    intro i; by_cases h : i∈X
    · exact ⟨Sum.inr ⟨i,h⟩,rfl⟩
    exact ⟨Sum.inl ⟨i,mem_compl.mpr h⟩,rfl⟩
  have hv : X = univ.map s := by ext i; simp [s]
  have ht : vol X = pass s (vol univ) := by rw [pass_vol, ← hv]
  rw [ht]; change ber A (pass t (gauss _) * pass s (vol _)) = _; rw [complementary ↥Xᶜ X t s hu,ber_top,mul_one]; exact det_amplitude _
end YM.Massive.Saturate
