import YM.Massive.Pressure.Interior
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Simultaneous Bpressure selector

Uniform *exponential in that stop's volume* retained, with constants, as soon as
that original common-mass lower and the analytic-family upper bounds are in place,
even though the price (e.g. volume) can be bigger at some stops than others. Need
exact transport on the complex disk (provide relation by continuous nonvanishing factors).
Preservation of **one** parameter by the analytic selection for all stops.

The version here is for any set of stops with the indicated hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Set Filter Function Complex Metric InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
open Disk

variable {M : Type*} (i : M) {f g : M → ℂ → ℂ}

/-- Relative ratio to i GIVEN. e.g., unit shifts, rescaling jacobians and
β units, all depending on step. -/
structure Joint (i : M) (f g : M → ℂ → ℂ) : Prop where
  cost m : Valid (f m)
  ratio m : ContinuousOn (g m) closedD
  zeroFree m x (h : x ∈ closedD) : g m x≠0
  normal m x (h : x ∈ closedD) : f m x=g m x*f i x

variable {i} (h : Joint i f g)

namespace Joint
include h
lemma peel {p : ℂ} (hp : p∈core) (hz : f i p=0) : Joint i (fun m => edited (f m) p) g := by
   have he m : f m p=0:=by rw [h.normal m p (open_closed (within hp)),hz,mul_zero]
   have hd m := Disk.edit hp (h.cost m) (he m)
   refine ⟨hd,h.ratio,h.zeroFree,?_⟩
   intro m x hx
   have hi (x : ℂ) (hx : x ∈ closedD) (hc : x≠p) : edited (f m) p x = g m x*edited (f i) p x:= by
      apply mul_left_cancel₀ (show factor p x≠0 from div_ne_zero (sub_ne_zero.mpr hc) (Disk.nonpole hp hx))
      rw [← reconstruct hp (he m) x hx,mul_left_comm, ← reconstruct hp hz x hx,h.normal m x hx]
   by_cases ha : x=p
   · subst x
     have hh : ∀ᶠ x in 𝓝[≠] p, edited (f m) p x = g m x*edited (f i) p x:= by
       filter_upwards [nhdsWithin_le_nhds (show closedD∈𝓝 p from Filter.mem_of_superset (isOpen_ball.mem_nhds (within hp)) open_closed), self_mem_nhdsWithin] with x hx ht; exact hi x hx ht
     have hy : closedD∈𝓝 p := Filter.mem_of_superset (isOpen_ball.mem_nhds (within hp)) open_closed
     exact tendsto_nhds_unique_of_eventuallyEq ((hd m).cont.continuousAt hy|>.continuousWithinAt) (((h.ratio m).continuousAt hy).mul ((hd i).cont.continuousAt hy)|>.continuousWithinAt) hh -- inspect
   exact hi x hx ha

lemma divided (n : ℕ) (hk : (3/4:ℝ)^n < ‖f i 0‖) :
    ∃ (f' : M → ℂ → ℂ) (l : List ℂ),
       Joint i f' g ∧ (∀ x∈l,x∈core) ∧ (∀ x∈core, f' i x≠0) ∧
       (∀ m, ∀ x∈ closedD, f m x=total l x*f' m x) := by
   induction n generalizing f with
   | zero => exact (hk.not_ge (show _ from (h.cost i).band 0 zero_closed)).elim -- power simp?
   | succ n ih =>
     classical
     by_cases he : ∀ p∈core, f i p≠0
     · exact ⟨f,[],h,by simp,he,fun m x _=>by simp [total]⟩
     push Not at he
     obtain ⟨p,hp,hz⟩:=he
     let k (m:M) := edited (f m) p
     have hf : (3/4:ℝ)^n < ‖k i 0‖:=by
        apply lt_of_mul_lt_mul_left _ (by norm_num : (0:ℝ)≤3/4)
        rw [reconstruct hp hz 0 zero_closed,norm_mul,pow_succ'] at hk
        exact hk.trans_le (mul_le_mul_of_nonneg_right (center hp) (norm_nonneg _))
     obtain ⟨f',l,hg,hL,hG,H⟩:= ih (h.peel hp hz) hf
     refine ⟨f',p::l,hg,fun x hx=> ?_,hG,fun m x hx=>?_⟩
     · simp only [List.mem_cons] at hx; rcases hx with h|h
       · exact h ▸ hp
       exact hL _ h
     rw [reconstruct hp (show f m p=0 from (h.normal m p (open_closed (within hp))).trans (by rw [hz,mul_zero])) _ hx,H m x hx,total,total,List.map_cons,List.prod_cons,mul_assoc]

/-- Use an integer power so also handles *very small* mass at the unmarked theory. -/
theorem selects (he : f i 0≠0) : ∃ x∈ Icc (1/2:ℝ) 1, ∀ m, ‖f m 0‖^21 ≤ ‖f m x‖:=by
   obtain ⟨n,hn⟩:= exists_pow_lt_of_lt_one (norm_pos_iff.mpr he) (by norm_num : (3/4:ℝ)<1) -- check
   obtain ⟨f',l,h',hC,hZ,H⟩:= divided h n hn
   obtain ⟨x,hx,hp⟩ := Disk.selection l hC
   have hu : ‖(x:ℂ)‖ ≤ 1:=by rw [norm_real,Real.norm_of_nonneg ((by norm_num : (0:ℝ)≤1/2).trans hx.1)]; exact hx.2
   have hm m : ∀ x∈core, f' m x≠0:=fun z hz=> by rw [h'.normal m z (open_closed (within hz))]; exact mul_ne_zero (h'.zeroFree _ _ (open_closed (within hz))) (hZ _ hz)
   refine ⟨x,hx,fun m=>?_⟩
   have hh:= origin l hC
   have hd : ‖total l 0‖ ≤ 1:= hh.trans (pow_le_one₀ (by norm_num) (by norm_num))
   have h₁ : ‖f m 0‖ ≤ ‖f' m 0‖:=by rw [H _ _ zero_closed,norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hd
   have h₂ : ‖f m 0‖ ≤ (3/4)^l.length :=by
      rw [H _ _ zero_closed,norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) ((h'.cost m).band _ zero_closed)).trans hh
   rw [H m x (closed.mpr (by linarith)),norm_mul]
   rw [show (21:ℕ)=16+5 from rfl,pow_add]; refine mul_le_mul ((pow_le_pow_left₀ (norm_nonneg _) h₂ 16).trans (?_ : _ ≤ ‖total l x‖)) ((pow_le_pow_left₀ (norm_nonneg _) h₁ 5).trans (harnack hu (h'.cost m) (hm m))) (by positivity) (norm_nonneg _) 
   apply le_trans _ hp; rw [← pow_mul,mul_comm l.length,pow_mul]
   apply pow_le_pow_left₀ (by norm_num) _
   have he:= Real.exp_one_lt_three; field_simp; linarith
end Joint
end YM.Massive.Pressure
