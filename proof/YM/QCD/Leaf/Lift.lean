import YM.QCD.Leaf.App
import YM.QCD.Garden.Lift

/-! # uniform own post estimates for re-sym saturated. Comparator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.LeafM
open Lat Function Lattice Wilson Kit Cost Run Rudder Finset RG Eyrie Stationary Sparks Revolve Paths Quarry Orbit Garden
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n: Side}{I:Type}{k B:ℕ}{C:I→Bloom k}{σ t η δ c p ξ:ℝ}
lemma rich (k)(hσ:0<σ)(ht:0≤t): ∃ δ p:ℝ,∃ B:ℕ,0<δ∧0<p∧∀ (V:Type)(A:V→Bloom k)(R:ℝ), Fractal A σ R→∀ ξ:ℝ,0<ξ→ξ≤1→∀ n b,B≤b → Own n (δ*ξ^2) t b (wild A ξ n) (p*R*ξ^k):=by
  obtain ⟨δ,P,B,hD,hP,H⟩:=postM k hσ ht
  refine ⟨δ,P,B,hD,hP,fun V A R h ξ hp ht' n b hB=> ?_⟩
  apply (Heritage.congregation (T:=fun i=> trackP (A i) ξ n) (mul_pos hD (by positivity)) ht (fun i=> H b hB ξ hp ht' n _ (h.sect i)) ((h.bills.mul_left P).mul_right (ξ^k)) (fun U=> (earns U h hp ht' hσ).of_norm.hasSum)).mono
  rw [tsum_mul_right,tsum_mul_left]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h.bill hP.le) (by positivity)
lemma richP (k)(hσ:0 < σ)(ht:0≤t): ∃ δ p:ℝ,∃ B:ℕ,0<δ∧0<p∧∀ (V:Type)(A:V→Bloom k)(R:ℝ), Fractal A σ R→∀ ξ:ℝ,0<ξ→ξ≤1→∀ n b,B ≤ b →Own n (δ*ξ^2) t b (wild (frosting A) ξ n) (p*R*ξ^k):=by
  have h : 0<σ/(1+(k:ℕ)):=div_pos hσ (by positivity)
  obtain ⟨δ,P,B,hD,hP,H⟩:=rich k h ht
  refine ⟨δ,P*Real.exp (σ*(2*k)),B,hD,by positivity,fun V A R hZ ξ hv hm n b hB=>?_⟩
  rw [mul_assoc P]; apply H (Fruited V) (frosting A) _ (coined _ h.le hZ ?_) ξ hv hm n b hB; rw [div_mul_cancel₀ _ (by positivity)]

open Filter Metric
-- actual local L2 matrix norm use exp
lemma tone_diff (e:Edge (Site n)): ContDiff ℝ ω (fun i:Cnr n=> colour (input su n i e)) :=by
  let L:Cnr n→ su.Color:=fun a=> (arm su n 1 a) (e.1,Exterior.coord e.2)
  have h:L=fun a=>_:=(rfl:L=L)
  let M:su.Color→ₗ[ℝ] Mat:=su.colorMat
  letI : NormedAlgebra ℚ Mat := .restrictScalars ℚ ℂ Mat
  have hd:ContDiff ℝ ω L:=(contDiff_apply ..).comp (arm su n 1).contDiff
  rw [show (fun i:Cnr n=> colour (input su n i e))=(fun i=> NormedSpace.exp (M (L i))) from ?_]
  · refine (show ContDiff ℝ ω (NormedSpace.exp (𝔸:=Mat)) from ?_).comp (M.toContinuousLinearMap.contDiff.comp hd); exact contDiff_iff_contDiffAt.mpr fun i=> (NormedSpace.exp_analytic (𝕂:=ℂ) (𝔸:=Mat) i).contDiffAt.restrict_scalars ℝ
  funext i; change su.mat (input su n i e)=_; change su.mat (Precision.represent _ _)=_; rw [YM.Work.F03.represent_link, Gauge.mat_lieExp]; rfl
lemma star_w (e:Edge (Site n)): ContDiff ℝ ω (fun i:Cnr n=> star (colour (input su n i e))) := (starL ℝ).contDiff.comp (tone_diff e)
lemma pulse_flow (n:Side): ContDiff ℝ ω (settled ∘ input su n):= (show ContDiff ℝ ω _ from contDiff_pi.2 (tone_diff (n:=n))).prodMk (contDiff_pi.2 (star_w (n:=n)))
lemma estate {X:Grid n→Sheet n}(h:Own n δ t B X c)(ht:0<δ):ContDiffAt ℝ ω (castF X) 0:=by
  obtain ⟨x,y,H⟩:=h
  have hz : settled (input su n (0:Cnr n))∈Kingdom n δ:=citizenship n ht _
  have hp: AnalyticAt ℂ (winch x) (settled (input su n 0)):=PolyDisc.finiteD _ (Filter.mem_of_superset ((country n δ).mem_nhds hz) H.won)
  have hx: castF X=winch x∘(settled∘input su n) :=funext fun i=> (H.winched ..).symm
  rw [hx]; exact (hp.contDiffAt.restrict_scalars ℝ).comp (f:= (settled ∘ input su n)) 0 (pulse_flow n).contDiffAt
end YM.QCD.Leaf.LeafM
