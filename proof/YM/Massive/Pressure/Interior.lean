import YM.Massive.Pressure.Disk
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-! # Log price for zero-free part and for real reading of all removed zeros -/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure.Disk
open Set Filter Function Complex Metric InnerProductSpace
open scoped Topology ComplexConjugate BigOperators

variable {f : ℂ → ℂ} {q : ℂ → ℝ} {z : ℂ} (hz : ‖z‖ ≤ 1)
include hz in
private theorem near : z ∈ ball (0:ℂ) (3/2:ℝ) := mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
include hz

private theorem poisson : ContinuousOn (poissonKernel 0 z) (sphere (0:ℂ) (3/2)) := by
   have he : ∀ w ∈ sphere (0:ℂ) (3/2), ‖w-z‖^2 ≠ 0 := fun w hw=> by
     have ht := near hz; exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Metric.sphere_disjoint_ball.ne_of_mem hw ht))) -- inspect
   unfold poissonKernel; simp only [sub_zero]; fun_prop (disch:=assumption)

private lemma limit (w : ℂ) (hw : w ∈ sphere (0:ℂ) (3/2)) : poissonKernel 0 z w ≤ 5 := by
   rw [poissonKernel_eq_re_herglotzRieszKernel]; apply (re_herglotzRieszKernel_le hw (near hz)).trans
   rw [sub_zero]; rw [div_le_iff₀ (by linarith)]; linarith

lemma harnack_bound (h : HarmonicOnNhd q core) (he : ∀ z∈core,0 ≤ q z) : q z ≤ 5*q 0 := by
   let R:ℝ:=3/2
   have hr : 0≤R:=by unfold R; norm_num
   let g := poissonKernel 0 z
   have hq : ContinuousOn q (sphere (0:ℂ) R):= h.contDiffOn.continuousOn.mono sphere_subset_closedBall
   have hs : ContinuousOn ((5:ℝ) • q) (sphere (0:ℂ) R):= hq.const_smul _
   have hh : ContinuousOn (g • q) (sphere (0:ℂ) R) := (poisson hz).smul hq
   have ht := Real.circleAverage_mono (hh.circleIntegrable hr) (hs.circleIntegrable hr) (fun w hw => ?_)
   · rw [Real.circleAverage_smul,h.circleAverage_poissonKernel_smul (near hz)] at ht -- inspect
     have hc : Real.circleAverage q 0 R=q 0 := HarmonicOnNhd.circleAverage_eq ((abs_of_nonneg hr).symm ▸ h)
     rw [hc] at ht; exact ht
   · rw [abs_of_nonneg hr] at hw
     exact mul_le_mul_of_nonneg_right (limit hz w hw) (he w (sphere_subset_closedBall hw))

/-- Uniform fixed power; f may have zeros outside the core. -/
theorem harnack (hf : Valid f) (h : ∀ x∈core,f x≠0) : ‖f 0‖^5 ≤ ‖f z‖ := by
   let q (w : ℂ) := -Real.log ‖f w‖
   have hc : HarmonicOnNhd q core := HarmonicOnNhd.neg (f:=fun w=> Real.log ‖f w‖)
      (fun x hx=>(hf.hol.analyticOnNhd isOpen_ball x (within hx)).harmonicAt_log_norm (h x hx))
   have hp (w) (hw : w∈core):0<‖f w‖:=norm_pos_iff.mpr (h w hw)
   have hl x (hx : x∈core) : 0 ≤ q x := neg_nonneg.mpr (Real.log_nonpos (hp _ hx).le (hf.band _ (open_closed (within hx))))
   apply (Real.log_le_log_iff (pow_pos (hp _ zero_core) _) (hp _ (ball_subset_closedBall (near hz)))).1
   rw [Real.log_pow]; have he:= harnack_bound hz hc hl; unfold q at he; push_cast; linarith

omit hz

def total (l : List ℂ) (x : ℂ) := (l.map fun y => factor y x).prod

lemma origin (l : List ℂ) (h : ∀ x∈l,x∈core) : ‖total l 0‖ ≤ (3/4:ℝ)^l.length := by
   induction l with
   | nil => simp [total]
   | cons p l ih =>
     rw [total,List.map_cons,List.prod_cons,norm_mul,List.length_cons,pow_succ']
     exact mul_le_mul (center (h p (by simp))) (ih (fun x hx=> h x (List.mem_cons_of_mem _ hx))) (norm_nonneg _) (by norm_num)

include hz in
lemma portfolio (l : List ℂ) (h : ∀ x∈l,x∈core) :
    (4:ℝ)⁻¹ ^ l.length * ‖product l z‖ ≤ ‖total l z‖ := by
   induction l with
   | nil => simp [product,total]
   | cons p l ih =>
     simp only [product,total,List.map_cons,List.prod_cons,norm_mul,List.length_cons,pow_succ']
     change _ * (_ * ‖product l z‖) ≤ _ * ‖total l z‖
     apply le_trans _ (mul_le_mul (estimate (h p (by simp)) hz)
           (ih fun x hx=>h x (List.mem_cons_of_mem _ hx)) (by positivity) (norm_nonneg _))
     exact le_of_eq (by ring)

lemma selection (l : List ℂ) (h : ∀ x∈l,x∈core) : ∃ x ∈ Icc (1/2:ℝ) 1,
    ((16*Real.exp 1:ℝ)⁻¹) ^ l.length ≤ ‖total l x‖ := by
   obtain ⟨x,hx,H⟩ := some_real l
   have he : ‖(x:ℂ)‖ ≤ 1 := by rw [norm_real, Real.norm_of_nonneg ((by norm_num : (0:ℝ) ≤ 1/2).trans hx.1)]; exact hx.2
   refine ⟨x,hx, le_trans ?_ (portfolio he l h)⟩
   apply le_trans _ (mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ ((4:ℝ)⁻¹) ^ l.length))
   rw [← mul_pow]; refine le_of_eq ?_; congr 1; field_simp
   ring
end YM.Massive.Pressure.Disk
