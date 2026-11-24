import YM.QCD.RP.Floor

/-! # Isometry on l¹ for these lattice theta copies

Using gamma convention with monomial columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Grass Lat NormedSpace Lattice Finset
open scoped Kronecker Matrix.Norms.Frobenius Matrix Topology BigOperators

private lemma atomics {A B : Type*} [Fintype A] [Fintype B] {f : Alg A → Alg B} (h : ∀ i : A, ‖f (atom i)‖ ≤ 1)
    (he : ∀ x y, ‖f (x*y)‖ ≤ ‖f x‖*‖f y‖) (h₁ : f 1=1) (s : Finset A) : ‖f (mono s)‖ ≤ 1 := by
  have hx (l : List A) : ‖f ((l.map atom).prod)‖ ≤ 1 := by
    induction l with
    | nil => simp [h₁]
    | cons x t ih => exact (he _ _).trans ((mul_le_mul (h x) ih (norm_nonneg _) zero_le_one).trans (by simp))
  obtain ⟨w,-,-,H⟩ := expression s
  rw [H]; simpa only [List.map_ofFn] using hx (List.ofFn w)

variable {n : Side} {F : ℕ} {R : Cells.Cut n} {C : Lat.Cut n F}
lemma roll_fields (T : Tape n) (x : Fields n F) : ‖T.tape F x‖ ≤ ‖x‖ := by
  conv_lhs => rw [← write x,map_sum]
  rw [norm_def x]; apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro i _
  rw [map_smul,norm_smul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply atomics (f:=⇑(T.tape F)) _ (fun _ _ => by rw [map_mul]; exact norm_mul_le ..) (map_one _)
  rintro (i|i)
  · change ‖T.tape F (psi i)‖ ≤ 1; rw [T.tape_psi,norm_smul,T.norm i.1.1]; simp [psi]
  change ‖T.tape F (bar i)‖ ≤ 1; rw [T.tape_bar,norm_smul,T.norm i.1.1]; simp [bar]
lemma roll_price (T : Tape n) (x : Insertion n F) : ‖T.roll x‖ ≤ ‖x‖ := by
  exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun i => (roll_fields T _).trans (ContinuousMap.norm_coe_le_norm x i)

lemma gamma_row₁ (a : Axis) (i : Pinor) : ∑ j, ‖gamma a i j‖=1 := by
  obtain ⟨i,k⟩ := i
  fin_cases a <;> fin_cases i <;> fin_cases k <;>
    norm_num [gamma,sx,sy,sz,Fintype.sum_prod_type,Fin.sum_univ_succ]
  all_goals exact (show ‖(1:ℂ)‖=1 from norm_one)
lemma glow_row (a : Axis) (i : Wind F) : ∑ j : Wind F, ‖glow a F i j‖=1 := by
  rw [Fintype.sum_prod_type]
  simp only [glow,lamp,copies,Matrix.blockDiagonal_apply,apply_ite (‖·‖),norm_zero, sum_ite_eq,mem_univ, if_true]
  erw [Fintype.sum_prod_type]
  simp only [wave,Matrix.kroneckerMap_apply,norm_mul,Matrix.one_apply,apply_ite (‖·‖),norm_zero,norm_one,
    mul_ite,mul_one,mul_zero,sum_ite_eq,mem_univ, if_true]
  exact gamma_row₁ ..
lemma glow_col (a : Axis) (i : Wind F) : ∑ j : Wind F, ‖glow a F j i‖=1 := by rw [← glow_star F a]; simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply, norm_star]; exact glow_row ..
lemma thin (x : Fields n F) : ‖theta R x‖ ≤ ‖x‖ := by
  conv_lhs => rw [← write x,map_sum]
  rw [norm_def x]; refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro s _
  rw [map_smulₛₗ,norm_smul,starRingEnd_apply,norm_star]
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply atomics (f:=⇑(theta R)) ?_ (fun _ _ => by rw [theta_mul,mul_comm]; exact norm_mul_le ..) (tilt_one _)
  rintro (⟨⟨u,i⟩,j⟩|⟨⟨u,i⟩,j⟩)
  · change ‖theta R (psi (place u (i,j)))‖ ≤ 1
    rw [theta_psi]; apply (norm_sum_le _ _).trans; simp [norm_smul, bar,glow_col]
  change ‖theta R (bar (place u (i,j)))‖ ≤ 1
  rw [theta_bar]; apply (norm_sum_le _ _).trans; simp [norm_smul, psi,glow_row]
lemma pic_le (x : Insertion n F) : ‖picture R C x‖ ≤ ‖x‖ := by
  have he (x : Insertion n F) : ‖reflect R x‖ ≤ ‖x‖ := (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    fun i => (thin (R:=R) _).trans (ContinuousMap.norm_coe_le_norm x _)
  exact (roll_price _ _).trans ((he _).trans (roll_price _ _))
lemma pic_price (x : Insertion n F) : ‖picture R C x‖=‖x‖ := le_antisymm (pic_le _) (by
  have h := pic_le (C:=C) (R:=R) (picture R C x); rwa [pictured] at h)
end YM.QCD.RP
