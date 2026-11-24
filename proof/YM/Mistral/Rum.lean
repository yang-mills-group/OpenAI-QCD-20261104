import YM.Mistral.Yester
import YM.Mistral.Glow
-- Omega pose.Info.S primitive properties on W. power receipts sharp.No PC.L.F_λ actual moments.
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function Set Metric Filter QCD Lat Lattice UV Patria Patria.Depth
open Poised Plans Plans.Stamp Intag Intag.Vale Finset
open scoped Topology BigOperators Matrix ComplexOrder ContDiff Classical
variable {d:ℕ}
open Needle Needle.GaugeP Hub YM.Fir YM.Massive.Fir
variable {C:Sequence}{P:Calibration C} {n m:ℕ}
variable {β e:ℝ}(hp:C.Path β e) (W: Choir)
variable (v w:W.W)
-- wrapper convex.Combine.Q.Inc Annulus.r stamps capped.A.Env.Balanced.
variable (f:Stokes d→W.W)(q:Stokes d→ℂ)(J:Patrol P)
variable (Y V R:ℝ)(x:E4)
open Patrol
noncomputable def beamρ (p:Patrol P): W.W→ₗ[ℂ]ℂ:= (W.total (p.size+2) (points (Fin.cons x (Fin.cons 0 p.land)))).toLinearMap (Fin.cons 0 (Fin.cons v (fun j=> W.focus none _ (p.texts j)))) 0
lemma pleads (w:W.W): beamρ W v x J w=Patrol.gleam J W x w v:=by
      apply congr_arg (W.total _ _); ext1 i; cases i using Fin.cases <;> simp
noncomputable def visionR (p:Patrol P) : W.W→ₗ[ℂ] ℂ:= (W.total (p.size+1) (points (Fin.cons 0 p.land))).toLinearMap (Fin.cons 0 (fun i=> W.focus none _ (p.texts i))) 0
lemma who(p:W.W): visionR W J p= Patrol.glory J W p:=by
      apply congr_arg (W.total _ _); ext1 i; cases i using Fin.cases <;> simp
local notation "Tx" k:arg=> Patrol.gleam J W x k v
variable (hQ:w=∑ i,q i • f i)(hf:0<V)(hy:0≤Y)(hX:∀ i,‖q i‖≤ V)
local notation "A"=> Stokes d
include hX hf hy hQ
lemma sufficed (p:A→ W.W) (h:∀ i,q i≠0 → ‖(↑(V*R^4):ℂ)*Patrol.gleam J W x (f i) v-Patrol.glory J W (p i)‖≤ Y) : ‖(↑(R^4):ℂ)* Patrol.gleam J W x w v- Patrol.glory J W (∑ i:A, (q i/(V:ℂ)) • p i)‖ ≤ Fintype.card A * Y:=by
       let k:ℂ:=V; have hK:k≠0:=Complex.ofReal_ne_zero.mpr hf.ne'; let c(i):= q i/k; let X(i:A):= (↑(V*R^4):ℂ)*Patrol.gleam J W x (f i) v-Patrol.glory J W (p i)
       rw [show (↑(R^4):ℂ)* Patrol.gleam J W x w v- Patrol.glory J W (∑ i:A, (q i/(V:ℂ)) • p i)= ∑ i,c i*X i from ?_]; swap
       · rw[hQ]; simp_rw [←pleads,←who]; rw [map_sum,map_sum,mul_sum,←sum_sub_distrib]; apply sum_congr rfl; intro j _; unfold X c; rw [←pleads,←who,Complex.ofReal_mul,map_smul,map_smul,smul_eq_mul,smul_eq_mul]; unfold k; field_simp <;> ring
       refine (norm_sum_le ..).trans (le_trans (sum_le_sum (s:=univ) (g:=fun _=>Y) (fun i _=>?_)) (le_of_eq (by simp)))
       rw [norm_mul]; by_cases he:q i=0; · simpa only[c,he,zero_div,norm_zero,zero_mul] using hy
       refine le_trans (mul_le_mul_of_nonneg_left (h _ he) (norm_nonneg _)) ?_; apply mul_le_of_le_one_left hy; unfold c; rw [norm_div,show ‖k‖=V from (by unfold k; rw[Complex.norm_real, Real.norm_of_nonneg hf.le]),div_le_one hf]; exact hX _
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.sufficed
