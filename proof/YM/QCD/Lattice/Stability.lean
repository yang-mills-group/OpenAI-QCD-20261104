import YM.QCD.Lattice.Cut

/-!
# Volume power bounds at cutoff

Ferromagnetic bare β. Actual partition lower bound, hence existence of the normalized regulator,
also allowing a fixed range of negative bare counterterms for even flavor number. For odd
numbers we take `m ≥ 0`. No complex-measure step, contour comparison or UV-uniform pressure claim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lat
open Wilson Lattice Finset MeasureTheory Function Filter Grass
open scoped Topology BigOperators NNReal ENNReal Kronecker

variable {n : Side} {F : ℕ}

/-- same admissible microphone count at every size -/
abbrev sites (n : Side) := Fintype.card (Site n)

lemma row_count (n : Side) : Fintype.card (Row n) = sites n *12 := by
  unfold Row Fiber Pinor Hue sites; simp
lemma paid_edges (n : Side) : Fintype.card (Edge (Site n))= sites n *4 := by simp [Edge,sites,Axis]
-- use given count rather than need to compute
abbrev pl := Fintype.card PlaqAxes
lemma paid_faces (n : Side) : Fintype.card (Face (Per n))=sites n*pl := Fintype.card_prod ..

lemma plaquette_le (U : Grid n) : energy U ≤ 2*(sites n)*pl := by
  refine (sum_le_sum fun i _ => (su.price_range (faceValue U i)).2).trans (le_of_eq ?_)
  simp only [sum_const, card_univ, paid_faces,nsmul_eq_mul,Nat.cast_mul]; ring

lemma bare_le {β : ℝ} (hb : 0 ≤ β) (U : Grid n) : bare β U ≤ 1 := by
  unfold bare; rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (energy_nonneg U)

lemma bare_ge {β : ℝ} (hb : 0 ≤ β) (U : Grid n) : (Real.exp (-2*β*pl)) ^ sites n ≤ bare β U := by
  unfold bare; rw [← Real.exp_nat_mul, Real.exp_le_exp]; calc
    _ = -β * (2*sites n*pl) := by ring
    _ ≤ _ := mul_le_mul_of_nonpos_left (plaquette_le U) (by linarith)

lemma copies_row (M : Sheet n) (i : Modes n F) : ∑ j, ‖copies F M i j‖=∑ j, ‖M i.1 j‖ := by
  rw [Fintype.sum_prod_type]; simp only [copies,Matrix.blockDiagonal_apply,apply_ite (‖·‖), norm_zero, sum_ite_eq,mem_univ, ↓reduceIte]

-- explicit form also useful across RP planes
lemma hop_read (t : Site n) (U : Grid n) (a : Axis) i j : singleHop t U a i j =
    (if i.1+step a=j.1 then (lo a ⊗ₖ thread t U a i.1) i.2 j.2 else 0) +
    (if i.1-step a=j.1 then (hi a ⊗ₖ star (thread t U a (i.1-step a))) i.2 j.2 else 0) := by
  rw [singleHop,opp]; unfold onSpin shift
  simp_rw [ride_mul,Equiv.refl_apply,Equiv.refl_trans,lace,Matrix.add_apply,rr,hop,back]; rfl

lemma lean_row (t : Site n) (U : Grid n) (a) (i : Row n) : ∑ j, ‖singleHop t U a i j‖ ≤ 24 := by
  let s : Finset (Site n) := {i.1 + step a, i.1 - step a}
  rw [Fintype.sum_prod_type, ← sum_subset (subset_univ s) (fun x _ hx => ?_)]
  · refine (sum_le_sum (g := fun _ => (12:ℝ)) (fun x _ => (sum_le_sum fun j _ =>
      entry_norm_bound_of_unitary (hop_u t U a) i (x,j)).trans (le_of_eq ?_))).trans ?_
    · simp [Fiber,Pinor,Hue]
    simp only [sum_const,nsmul_eq_mul]
    have hc : s.card ≤ 2 := card_le_two
    have hp : (s.card:ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  apply sum_eq_zero; intro j _; have hm : x ≠ i.1+step a ∧ x ≠ i.1-step a := by simpa [s] using hx
  simp only [hop_read, if_neg hm.1.symm, if_neg hm.2.symm, add_zero,norm_zero]

lemma allotted (t : Site n) (U : Grid n) (m : ℝ) (i : Row n) : ∑ j, ‖bareD t U m i j‖ ≤ |m|+100 := by
  have h0 : (∑ j, ‖(1:Sheet n) i j‖)=1 := by simp [Matrix.one_apply,apply_ite (‖·‖)]
  have ha (j : Row n) : ‖bareD t U m i j‖ ≤ |m| * ‖(1:Sheet n) i j‖+
      ∑ a : Axis, (‖(1:Sheet n) i j‖+‖singleHop t U a i j‖) := by
    rw [bareD,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply]; simp_rw [Matrix.sub_apply]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ((norm_sum_le _ _).trans (sum_le_sum fun k _ => norm_sub_le _ _)))
    simp [norm_smul]
  refine (sum_le_sum fun j _ => ha j).trans ?_
  rw [sum_add_distrib,← mul_sum,h0,mul_one, sum_comm]; simp_rw [sum_add_distrib,h0]; gcongr
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ _ : Axis, ((1:ℝ) + 24) := sum_le_sum fun i _ => add_le_add_right (by exact lean_row _ _ _ _) _
    _ = _ := by norm_num [Axis]

namespace Cut
variable (C : Cut n F)

lemma grass_price (U : Grid n) : ‖C.insertD U‖ ≤ ((101+|C.m|) ^ (12*F)) ^ sites n := by
  refine (Grass.gauss_norm _).trans ((prod_le_prod (g := fun i : Modes n F => 101+|C.m|) ?_ ?_).trans (le_of_eq ?_))
  · intro i _; positivity
  · -- constant per variable, l1 used to absorb insertions
    refine fun i _ => (show _ ≤ 101+|C.m| from ?_)
    rw [ferm,copies_row]; have ht := allotted C.t U C.m i.1; linarith
  simp only [prod_const,card_univ, Modes, Fintype.card_prod, Flavor, Fintype.card_fin, row_count]
  rw [← pow_mul]; ring

lemma test_price (hb : 0 ≤ C.β) (x : Insertion n F) :
    ‖C.raw x‖ ≤ (((101+|C.m|)^(12*F))^(sites n)) * ‖x‖ := by
  change ‖∫ U, _ ∂prior su n‖ ≤ _
  refine (norm_integral_le_of_norm_le (integrable_const (μ:=prior su n) ((((101+|C.m|)^(12*F))^(sites n)) * ‖x‖)) ?_).trans (by simp)
  filter_upwards with U
  unfold rate; rw [norm_mul,Complex.norm_real, Real.norm_eq_abs,abs_of_pos (bare_pos ..),ContinuousMap.mul_apply]
  refine (mul_le_mul (bare_le hb U) ((price _).trans (norm_mul_le _ _)) (norm_nonneg _) zero_le_one).trans ?_
  rw [one_mul]
  exact mul_le_mul (C.grass_price _) (ContinuousMap.norm_coe_le_norm x U) (norm_nonneg _) (by positivity)

lemma real_nn (he : 0 ≤ C.m ∨ Even F) (U : Grid n) : 0 ≤ C.rateR U := by
  refine mul_nonneg (bare_pos ..).le ?_; rcases he with he|he
  · exact pow_nonneg (det_sign _ U he) _
  exact he.pow_nonneg _
end Cut

private lemma rectangle (S T : Set su.El) :
    {U : Grid n | aligns S T U} = Set.univ.pi (fun x : Edge (Site n) =>
      if x.2=0 then S else if x.2=1 then T else Set.univ) := by
  ext U
  constructor
  · rintro (h : aligns S T _); rintro ⟨x,i⟩ -
    by_cases h0 : i=0; · simpa only [h0,↓reduceIte] using (h x).1
    by_cases h1 : i=1; · simpa only [h1, one_ne_zero,↓reduceIte] using (h x).2
    simp [h0,h1]
  intro he x
  have hp := he (x,0) (Set.mem_univ _)
  have ht := he (x,1) (Set.mem_univ _)
  exact ⟨by simpa using hp,by simpa using ht⟩

lemma seasonal (S T : Set su.El) (hS : S.Nonempty) (hT : T.Nonempty) (hs : IsOpen S) (ht : IsOpen T) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : Side,
      b ^ sites n ≤ (prior su n).real {U : Grid n | aligns S T U} ∧ MeasurableSet {U : Grid n | aligns S T U} := by
  let H (i : Axis) := if i=0 then S else if i=1 then T else Set.univ
  have ho i : IsOpen (H i) := by unfold H; split_ifs <;> first | assumption | exact isOpen_univ
  have hp i : (H i).Nonempty := by unfold H; split_ifs <;> first | assumption | exact Set.univ_nonempty
  have hv i : 0 < su.probHaar.real (H i) := ENNReal.toReal_pos ((ho i).measure_pos _ (hp i)).ne' (measure_ne_top _ _)
  refine ⟨∏ i : Axis, su.probHaar.real (H i), prod_pos (fun i _ => hv i), ?_⟩
  intro n; rw [rectangle]; constructor
  · refine le_of_eq ?_; unfold Measure.real prior; rw [Measure.pi_pi, ENNReal.toReal_prod,Fintype.prod_prod_type]; exact (Finset.prod_const (b:= (∏ x : Axis, (su.probHaar (H x)).toReal))).symm
  exact (isOpen_set_pi Set.finite_univ fun i _ => ho i.2).measurableSet

/-- Simultaneous lower witnesses. Odd flavors covered here for nonnegative tree mass only. -/
theorem stable : ∃ c b : ℝ, 0<c ∧ 0<b ∧ ∀ n F (C : Cut n F), 0 ≤ C.β →
    (0 ≤ C.m ∨ -c ≤ C.m ∧ Even F) →
    (b * (Real.exp (-2*C.β*pl)*c^(12*F))) ^ sites n ≤ C.partitionR ∧ 0 < C.partitionR := by
  obtain ⟨S,T,hS,hT,hs,ht,c,hc,K⟩ := patch
  obtain ⟨b,hb,hw⟩ := seasonal S T ⟨_,hs⟩ ⟨_,ht⟩ hS hT
  refine ⟨c,b,hc,hb,?_⟩
  intro n F C hB hF
  have hm : -c ≤ C.m := hF.elim (by intro h; linarith) And.left
  let f := (Real.exp (-2*C.β*pl)*c^(12*F)) ^ sites n
  let R := {U : Grid n | aligns S T U}
  have hk (U) (hu : U ∈ R) : f ≤ C.rateR U := by
    unfold f; rw [Cut.rateR, mul_pow]
    have hx := (K _ C.t _ hm U hu).2
    rw [row_count] at hx
    refine mul_le_mul (bare_ge hB U) ?_ (by positivity) (bare_pos ..).le
    exact (le_of_eq (show _ = (c^(sites n * 12))^F by simp only [← pow_mul]; ring)).trans (pow_le_pow_left₀ (by positivity) hx _)
  have hpp : _ := setIntegral_mono_on (f:=fun _ => f) (μ:=prior su n) (integrable_const _) C.real_pay.integrableOn
    (hw n).2 hk
  have hi : (0: Grid n → ℝ) ≤ᵐ[prior su n] C.rateR := Eventually.of_forall (C.real_nn (hF.imp_right And.right))
  have hl := hpp.trans (setIntegral_le_integral C.real_pay hi)
  rw [← Cut.located,setIntegral_const,smul_eq_mul] at hl
  rw [mul_pow]
  have hj : b ^ sites n * f ≤ C.partitionR := (mul_le_mul_of_nonneg_right (hw n).1 (show 0 ≤ f by unfold f; positivity)).trans hl
  exact ⟨hj, lt_of_lt_of_le (by unfold f; positivity) hj⟩

lemma normalized (C : Cut n F) (hc : 0 ≤ C.β) (hp : 0 ≤ C.m) :
    0<C.partitionR ∧ C.average 1=1 := by
  obtain ⟨_,_,_,_,H⟩ := stable
  have h := (H _ _ C hc (.inl hp)).2
  exact ⟨h,C.vacuum h⟩

end YM.QCD.Lat
