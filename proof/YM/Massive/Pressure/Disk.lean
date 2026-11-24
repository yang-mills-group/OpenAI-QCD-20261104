import YM.Massive.Pressure.Samples
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Harmonic.Poisson

/-!
# Universal disk estimates for lower-pressure selection

Keep DifferentiableOn hypothesis only on the *open* disk. Blaschke factoring
must remove exactly the singularity also at the zeros. Preserve *same* supremum
bound at each factor. Use a generous but fixed interior (r=1.5), real samples
only through [1/2,1].
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Set Filter Function Complex Metric InnerProductSpace
open scoped Topology ComplexConjugate BigOperators

def D := ball (0:ℂ) 2
def closedD := closedBall (0:ℂ) 2
def core := closedBall (0:ℂ) (3/2)

@[simp] lemma closed {x : ℂ} : x ∈ closedD ↔ ‖x‖ ≤ 2 := by simp [closedD]
@[simp] lemma opened {x : ℂ} : x ∈ D ↔ ‖x‖ < 2 := by simp [D]
@[simp] lemma inside {x : ℂ} : x ∈ core ↔ ‖x‖ ≤ 3/2 := by simp [core]
lemma open_closed : D ⊆ closedD := ball_subset_closedBall
lemma within : core ⊆ D := closedBall_subset_ball (by norm_num)
lemma closure_eq : closure D = closedD := closure_ball _ (by norm_num)
@[simp] lemma zero_core : 0 ∈ core := by norm_num
@[simp] lemma zero_closed : 0 ∈ closedD := open_closed (within zero_core)

namespace Disk

def Q (p z : ℂ) := (4-star p*z)/2

def factor (p z : ℂ) := (z-p)/Q p z

variable {p z : ℂ} (hp : p ∈ core)
include hp

lemma nonpole (hz : z ∈ closedD) : Q p z ≠ 0 := by
    apply div_ne_zero _ (by norm_num)
    apply sub_ne_zero.mpr
    refine fun he => (show ‖star p*z‖ < ‖(4:ℂ)‖ from ?_).ne (congr_arg (‖·‖) he.symm)
    rw [norm_mul,norm_star]
    apply lt_of_le_of_lt (mul_le_mul (inside.mp hp) (closed.mp hz) (norm_nonneg _) (by norm_num))
    norm_num

lemma circle_factor {z : ℂ} (hz : ‖z‖=2) : ‖factor p z‖=1 := by
    unfold factor Q; rw [norm_div, norm_div]; norm_num
    have h : ‖(4:ℂ)-star p*z‖=2*‖z-p‖:= by
      have he : (4:ℂ)-star p*z = (star (z-p))*z := by
         rw [star_sub,sub_mul]; congr 1; rw [Complex.star_def,mul_comm (conj z),mul_conj, normSq_eq_norm_sq,hz]; norm_num
      rw [he,norm_mul,norm_star,hz,mul_comm]
    have ht := inside.mp hp; have hf : 0 < ‖z-p‖:= by apply norm_pos_iff.mpr; intro e; have he := norm_nonneg (z-p); rw [sub_eq_zero.mp e] at hz; linarith
    change ‖z-p‖ / (‖(4:ℂ)-star p*z‖/2)=1; rw [h]; field_simp

lemma center : ‖factor p 0‖ ≤ 3/4 := by
    have he := inside.mp hp; unfold factor Q; simp; linarith

lemma estimate (h : ‖z‖ ≤ 1) : (4:ℝ)⁻¹*‖z-p‖ ≤ ‖factor p z‖ := by
    have hk := inside.mp hp
    have he : 0< ‖Q p z‖:= norm_pos_iff.mpr (nonpole hp (closed.mpr (by linarith)))
    have ht : ‖Q p z‖≤4:=by
      unfold Q; rw [norm_div];
      have hh:= norm_sub_le (4:ℂ) (star p*z); rw [norm_mul,norm_star] at hh
      norm_num at hh ⊢; nlinarith [norm_nonneg z,norm_nonneg p]
    rw [factor,norm_div,le_div_iff₀ he]; exact (mul_le_mul_of_nonneg_left ht (by positivity : 0≤4⁻¹ * ‖z-p‖)).trans_eq (by ring)

omit hp
variable {f : ℂ → ℂ}

structure Valid (f : ℂ → ℂ) : Prop where
  hol : DifferentiableOn ℂ f D
  cont : ContinuousOn f closedD
  band x (h : x ∈ closedD) : ‖f x‖ ≤ 1

def edited (f : ℂ → ℂ) (p z : ℂ) := Q p z * dslope f p z
variable (h : Valid f) (hf : f p=0)
include hf hp

lemma reconstruct (z : ℂ) (hz : z∈ closedD) : f z=factor p z * edited f p z := by
    unfold factor edited
    by_cases he : z=p
    · subst z; simp [hf]
    rw [← mul_assoc,div_mul_cancel₀ _ (nonpole hp hz),dslope_of_ne _ he,slope_def_module,hf,sub_zero,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ (sub_ne_zero.mpr he),one_mul]

include h
lemma edit : Valid (edited f p) := by
    have ht := within hp; have hm : D ∈ 𝓝 p := isOpen_ball.mem_nhds ht
    have hq : Differentiable ℂ (Q p) := by unfold Q; fun_prop
    have hc : closedD ∈ 𝓝 p:= Filter.mem_of_superset hm open_closed
    have hd : DifferentiableOn ℂ (edited f p) D := hq.differentiableOn.mul ((Complex.differentiableOn_dslope hm).mpr h.hol)
    have hk : ContinuousOn (edited f p) closedD:= hq.continuous.continuousOn.mul ((continuousOn_dslope hc).2 ⟨h.cont,h.hol.differentiableAt hm⟩)
    refine ⟨hd,hk, fun x hx=>?_⟩
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball (x:=(0:ℂ)) (r:=2)) (show DiffContOnCl ℂ (edited f p) D from ⟨hd,closure_eq.symm ▸ hk⟩) _ (closure_eq.symm ▸ hx)
    intro z hz
    replace hz : z∈sphere 0 2:= frontier_ball (E:=ℂ) _ (by norm_num : (2:ℝ)≠0) ▸ hz
    have he : z∈ closedD:= sphere_subset_closedBall hz
    have ht := h.band z he; rwa [reconstruct hp hf z he,norm_mul,circle_factor hp (by simpa only [mem_sphere,dist_zero_right] using hz),one_mul] at ht

end Disk
end YM.Massive.Pressure
