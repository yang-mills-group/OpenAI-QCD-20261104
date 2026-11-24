import YM.QCD.Pearl.Canyon

/-!
# Continuum radial detector. Positive beta correction to coarse precision (screening).
Angular facts with ordinary Euclidean volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch MeasureTheory Stationary
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff ENNReal
variable {n: Side} {μ : ℝ}

def windward (k:Gₐ):= f0 (ix k) 0-f0 (ix k) 1
lemma gaz (k:Gₐ): windward k=12*(( (2*(k 1)^2-‖k‖^2)*4*((k 0)^2-(k 1)^2)+2*((k 0)^2+(k 1)^2)*‖k‖^2)/‖k‖^8):=by
  have he: lensq (ix k)= ‖k‖^2:= (fry_sq (ix k)).symm.trans (by rw [← radius]); unfold windward f0 hopC capital; rw [he]; simp only [if_true, if_neg (show ¬(0:Axis)=1 from by decide)];
  change 12*(((2:ℝ)*_ -_)*(_-_)- (- k 0)*(2*k 0)*_)/ _ -12*((2*(k 1)^2-_)*(_-_)- k 1*(2*k 1)*_)/ _= _
  rw [show ix k 1=k 1 from rfl, show ix k 0=k 0 from rfl]; ring
lemma gaz_i (k:Gₐ) (h:0<‖k‖): windward k=12*(8*jetMix k 0 1 -8*opJen (springAx 1) k 4- 2*opJen (springAx 0) k 2+6*opJen (springAx 1) k 2):=by
  rw [gaz]; simp only [jetMix,opJen,springTouch]; field_simp; ring
lemma south (h : 0<μ): IntegrableOn windward (orbShell μ) volume := by
  simp_rw [funext gaz];
  exact (geoS h _ (show Continuous fun k:Gₐ=> ( (2*(k 1)^2-‖k‖^2)*4*((k 0)^2-(k 1)^2)+2*((k 0)^2+(k 1)^2)*‖k‖^2) from by fun_prop) 8).const_mul _
lemma full_pole (h : 0<μ) (he:μ≤1): ∫ x in orbShell μ, windward x=4*(2*Real.pi^2*Real.log μ⁻¹):=by
  have h₁ (i: Axis)(m):= joy_paid h (springAx i) m
  have h₂:=(joy_meal h 0 1).const_mul (8:ℝ)
  let f x:=8*jetMix x 0 1-8*opJen (springAx 1) x 4-2*opJen (springAx 0) x 2
  rw [setIntegral_congr_fun shell_meas (fun x hx=> gaz_i x (h.trans hx.1)), integral_const_mul];
  have he': IntegrableOn (fun x=>8*jetMix x 0 1-8*opJen (springAx 1) x 4) (orbShell μ) volume:= Integrable.sub h₂ ((h₁ 1 4).const_mul _)
  rw [integral_add (show Integrable f (volume.restrict (orbShell μ)) from he'.sub ((h₁ 0 2).const_mul _)) ((h₁ 1 2).const_mul 6), integral_sub he' ((h₁ 0 2).const_mul 2), integral_sub h₂ ((h₁ 1 4).const_mul 8)]; simp_rw [integral_const_mul]
  have hu : joyMix μ 1 0=joyMix μ 0 1:=by unfold joyMix; congr 1; funext x; unfold jetMix; ring
  change 12*(8*joyMix μ 0 1-8*joyAx μ (springAx 1) 4 - 2 * joyAx μ (springAx 0) 2 + 6*joyAx μ (springAx 1) 2)=_
  rw [joy_knot h 1 0 (by decide),hu,joy_heights h _ _ (by decide), joy_two h,joy_two h,landX]; simp only [snowY]; rw [polar_m μ h he]; ring
lemma gale (k:Gₐ):‖windward k‖≤ 300*radial 4 k:=by
  let d:=‖k‖; let X:=k 0; let Y:=k 1
  have hx:X^2≤d^2:= (ordinate (ix k) 0).trans_eq ((fry_sq _).symm.trans (by rw [← radius]))
  have hy:Y^2≤d^2:=(ordinate (ix k) 1).trans_eq ((fry_sq _).symm.trans (by rw [← radius]))
  have h1: |2*Y^2-d^2| ≤ d^2:=by rw [abs_le]; constructor <;> nlinarith
  have h2:|X^2-Y^2| ≤ d^2:=by rw [abs_le]; constructor <;> nlinarith
  have hh: |( (2*Y^2 -d^2)*4*(X^2-Y^2)+2*(X^2+Y^2)*d^2)|≤ 8*d^4:=by
    refine (abs_add_le ..).trans ?_
    apply add_le_add (b:= d^2*4*d^2) (d:=4*d^4) _ _ |>.trans_eq (by ring)
    · rw [abs_mul,abs_mul]; gcongr; norm_num
    rw [abs_of_nonneg (by positivity)]; calc _ ≤ 2*(d^2+d^2)*d^2:=by gcongr
                                              _ = _:=by ring
  rw [gaz]; dsimp only [radial]; rw [Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<12),abs_of_nonneg (by positivity : 0≤ ‖k‖^8)];
  change 12*(_/d^8)≤300*(d^4)⁻¹
  by_cases he:d=0; · rw [he]; norm_num
  have hp:0<d:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh (by positivity)) (by norm_num : (0:ℝ)≤12)).trans; field_simp; linarith
lemma scales (k:Gₐ)(t : ℝ) (h : 0<t): windward (t • k)= (t^4)⁻¹*windward k:=by
  simp_rw [gaz,norm_smul,Real.norm_of_nonneg h.le]; change _= _
  simp only [PiLp.smul_apply,smul_eq_mul]; by_cases he:k=0; · subst k; simp
  field_simp -- maybe inv nonzero not required
lemma sail_h (k:Gₐ) (he:k≠0): ContDiffAt ℝ ω windward k:=by simp_rw [funext gaz]; have hx : ContDiffAt ℝ ω (fun a:Gₐ=> ‖a‖) k:=contDiffAt_norm ℝ he; fun_prop (disch:=positivity)

-- Compact shell unit scale
lemma sway :∃ C : ℝ,0≤ C∧∀ k x:Gₐ, ‖k‖=1 → ‖x-k‖≤1/2 → ‖windward x-windward k‖ ≤ C*‖x-k‖:=by
  let D := closedBall (0:Gₐ) 2 \ ball 0 (1/2)
  have hD:IsCompact D:= IsCompact.of_isClosed_subset (isCompact_closedBall (0:Gₐ) 2) (isClosed_closedBall.inter isOpen_ball.isClosed_compl) Set.diff_subset
  have hx z (hz:z∈D): z≠0:=fun ht=> hz.2 (ht ▸ mem_ball_self (by norm_num))
  have ht: ContinuousOn (fun x=> ‖fderiv ℝ windward x‖) D:= ContinuousOn.norm fun x hx'=> (((sail_h x (hx _ hx')).fderiv_right (m:=ω) (by simp)).continuousAt.continuousWithinAt)
  obtain ⟨C,h⟩:= (hD.image_of_continuousOn ht).bddAbove
  refine ⟨|C|,abs_nonneg _,fun k x hk hr=>?_⟩
  have hh: closedBall k (1/2)⊆ D:=by
    intro z hz; rw [mem_closedBall,dist_eq_norm] at hz
    refine ⟨?_,?_⟩; · rw [mem_closedBall,dist_zero_right]; linarith [(norm_sub_norm_le z k)]
    rw [mem_ball_zero_iff]; have ht:= (norm_sub_norm_le k z).trans ((norm_sub_rev z k).symm.le.trans hz); linarith
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun i hi=> ((sail_h i (hx i (hh hi))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt) (fun i hi=> (h ⟨i,hh hi,rfl⟩).trans (le_abs_self C)) (convex_closedBall k (1/2)) (mem_closedBall_self (by norm_num)) (by rwa [mem_closedBall,dist_eq_norm])
lemma sway2 :∃ C : ℝ,0≤C∧∀ k x:Gₐ,0<‖k‖ → ‖x-k‖≤‖k‖/2 → ‖windward x-windward k‖ ≤ C*radial 5 k * ‖x-k‖:=by
  obtain ⟨C,hc,H⟩:=sway; refine ⟨C,hc,fun k x hk he=>?_⟩
  have hL : 0<‖k‖⁻¹:=by positivity
  have hh : ‖‖k‖⁻¹ • x-‖k‖⁻¹ • k‖=‖k‖⁻¹*‖x-k‖:= by rw [← smul_sub,norm_smul,Real.norm_of_nonneg hL.le]
  have ht:= H (‖k‖⁻¹ • k) (‖k‖⁻¹ • x) (by rw [norm_smul,Real.norm_of_nonneg hL.le,inv_mul_cancel₀ hk.ne']) (by rw [hh,inv_mul_eq_div,div_le_iff₀ hk]; linarith)
  rw [hh, scales k _ hL,scales x _ hL,← mul_sub,norm_mul, Real.norm_of_nonneg (by positivity), inv_pow,inv_inv,mul_comm (‖k‖^4)] at ht; unfold radial; apply (le_div_iff₀ (by positivity : 0<‖k‖^4)).mpr ht |>.trans_eq; ring
end YM.QCD.Pearl
