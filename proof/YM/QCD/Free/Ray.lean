import YM.QCD.Free.Rotation

/-! # Origin jet and scaling limit on the unit torus Fourier multiplier -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Free
open Lattice Wilson Lat Function Finset Filter
open scoped Matrix.Norms.L2Operator Topology BigOperators

lemma slope (p : Freq) : Tendsto (fun r : ℝ => (r:ℂ)⁻¹ • display (r • p) 0) (𝓝[≠] 0) (𝓝 (jet p)) := by
  have he (a : Axis) : HasDerivAt (fun r : ℝ => r*p a) (p a) 0 := by
    simpa using! (hasDerivAt_id (0:ℝ)).mul_const (p a)
  have hc (a) : HasDerivAt (fun r : ℝ => 1-Real.cos (r*p a)) 0 0 := by simpa using! ((hasDerivAt_const 0 (1:ℝ)).sub (he a).cos)
  have hs (a) : HasDerivAt (fun r : ℝ => Real.sin (r*p a)) (p a) 0 := by simpa using! (he a).sin
  have hw : HasDerivAt (fun r : ℝ => wmass (r • p)) 0 0 := by
    have h := HasDerivAt.fun_sum (u:=univ) (fun a _ => hc a)
    simpa only [sum_const_zero] using! h
  have hm : Tendsto (fun r : ℝ => (r:ℂ)⁻¹ • ((wmass (r • p):ℂ) • (1:Bundle))) (𝓝[≠] 0) (𝓝 0) := by
    have hu := hasDerivAt_iff_tendsto_slope_zero.mp hw
    have he : Tendsto (fun r : ℝ => r⁻¹ * wmass (r • p)) (𝓝[≠] 0) (𝓝 0) := by simpa [smul_eq_mul,wmass] using hu
    simp only [smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    exact (by simpa only [Complex.ofReal_zero,zero_smul] using! ((Complex.continuous_ofReal.tendsto 0).comp he).smul_const (1:Bundle))
  have hz (a) : Tendsto (fun r : ℝ => (r:ℂ)⁻¹ • ((sine (r • p) a : ℂ) • wave (gamma a))) (𝓝[≠] 0) (𝓝 ((p a:ℂ) • wave (gamma a))) := by
    have hu : Tendsto (fun r : ℝ => r⁻¹ * sine (r • p) a) (𝓝[≠] 0) (𝓝 (p a)) := by simpa [smul_eq_mul,sine] using hasDerivAt_iff_tendsto_slope_zero.mp (hs a)
    simp only [smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    exact ((Complex.continuous_ofReal.tendsto _).comp hu).smul_const _
  simp_rw [display,jet,zero_add,smul_add,fun (r : ℝ) => smul_comm (r:ℂ)⁻¹ Complex.I (slash (sine (r • p))),slash,smul_sum]
  simpa only [smul_sum,zero_add] using hm.add ((tendsto_finsetSum univ fun a _ => hz a).const_smul Complex.I)

lemma backjet (p : Freq) (hp : p≠0) : Tendsto (fun r : ℝ => ((r:ℂ)⁻¹ • display (r • p) 0)⁻¹) (𝓝[≠] 0) (𝓝 (jet p)⁻¹) := by
  refine (continuousAt_matrix_inv (jet p) ?_).tendsto.comp (slope p)
  rw [show Ring.inverse = fun x : ℂ => x⁻¹ from funext Ring.inverse_eq_inv]
  exact continuousAt_inv₀ (jet_inv hp).ne_zero

lemma fixed_nz (p : Cover) : fixed p ≠ 0 := by
  intro h
  have ht := fixed_lower p 0; rw [h,Pi.zero_apply,abs_zero] at ht; exact (not_le.mpr Real.pi_pos) ht

lemma exhausting : Tendsto (fun (n:Side) => n.val) atTop atTop := by
  refine tendsto_atTop.2 fun i => (eventually_ge_atTop (⟨i+1,by omega⟩:Side)).mono fun n hn => ?_
  change i ≤ n.val; exact le_trans (by omega : i ≤ i+1) hn
lemma shrinks : Tendsto spacer atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr -- check
  refine ⟨tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp exhausting),Eventually.of_forall fun n => (fine n).ne'⟩
lemma lifts (p : Cover) : ∀ᶠ n in (atTop : Filter Side), lift (wrap n p)=p := by
  have hu (i : Axis) : ∀ᶠ n in (atTop : Filter Side), -(n.val:ℤ)<2*p i ∧ 2*p i ≤ n.val := by
    filter_upwards [exhausting.eventually (eventually_gt_atTop (2*(p i).natAbs))] with n hn; change 2*_ < n.val at hn; omega
  filter_upwards [eventually_all.mpr hu] with n hn; exact lift_eq_iff.mpr ⟨rfl, hn⟩
lemma flip_slope (n : Side) (p : Site n) : ((spacer n:ℂ)⁻¹ • display (menu p) 0)⁻¹=(spacer n:ℂ) • (display (menu p) 0)⁻¹ := by
  have he := invert (menu_pos p (m:=0) le_rfl)
  have hh : (spacer n:ℂ)≠0 := by exact_mod_cast (fine n).ne'
  apply Matrix.inv_eq_right_inv -- check
  rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_nonsing_inv _ he,smul_smul,inv_mul_cancel₀ hh,one_smul]

lemma exposed (p : Cover) : Tendsto (fun n => (spacer n:ℂ) • (display (menu (wrap n p)) 0)⁻¹) atTop (𝓝 (jet (fixed p))⁻¹) := by
  refine ((backjet (fixed p) (fixed_nz p)).comp shrinks).congr' ?_
  filter_upwards [lifts p] with n hn; rw [← flip_slope, menu,hn]; rfl
end YM.QCD.Free
