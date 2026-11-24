import YM.Analysis.SmoothJets
import Mathlib.Topology.MetricSpace.Thickening
/-! If error decreases faster than grid weight powers and all higher derivatives have polynomial growth, all finite jets decrease rapidly too. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig.Video
open Function Set Filter Metric
open scoped Topology ContDiff BigOperators Classical
variable {X Y : Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable (f:X→ Y)
private def df := fderiv ℝ f
variable {x:X}{t M V:ℝ}
local notation "s"=> Metric.closedBall x t
-- difference estimate then recover op norm.
lemma roam (hp:0<t)(h:∀ y∈ closedBall x t,DifferentiableAt ℝ f y) (hX:∀ y∈closedBall x t, ‖df f y-df f x‖ ≤M)(he:0 ≤ M)(hY:∀ y∈closedBall x t, ‖f y‖ ≤ V): ‖fderiv ℝ f x‖ ≤ (V+V)/t+M:=by
     let F:= df f x
     have hx:x∈s:= mem_closedBall_self hp.le; have ht₀:0 ≤ V:=(norm_nonneg _).trans (hY x hx)
     refine ContinuousLinearMap.opNorm_le_bound (fderiv ℝ f x) (by positivity) fun z=>?_
     by_cases hz:z=0; · rw[hz, map_zero,norm_zero,norm_zero,mul_zero]
     let u:=‖z‖⁻¹ • z; have hk:‖u‖=1:=by unfold u; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
     let v:=t • u; have ht:‖v‖=t:=by unfold v; rw [norm_smul,Real.norm_of_nonneg hp.le,hk,mul_one]
     let y:=x+v; have hy:y∈s:=by unfold y; rw[mem_closedBall,dist_eq_norm,add_sub_cancel_left,ht]
     have hK:= Convex.norm_image_sub_le_of_norm_fderiv_le' (φ:=F) h hX (convex_closedBall ..) hx hy; rw[show y-x=v from add_sub_cancel_left ..,ht] at hK
     have hU : ‖F v‖ ≤ M*t+(V+V):=calc
          _ ≤ ‖F v - (f y-f x)‖ + ‖f y-f x‖:= (sub_le_iff_le_add.mp (norm_sub_norm_le ..))
          _ ≤ _:=add_le_add (by rw [norm_sub_rev]; exact hK) ((norm_sub_le ..).trans (add_le_add (hY y hy) (hY x hx)))
     have hv : ‖F u‖ ≤ (V+V)/t+M:= by rw [show F v=t • F u from map_smul ..,norm_smul,Real.norm_of_nonneg hp.le] at hU; field_simp; linarith only[hU] -- simplify
     have hp : F z= ‖z‖ • F u:=by unfold u; rw [map_smul,smul_inv_smul₀ (norm_ne_zero_iff.mpr hz)]
     change ‖F z‖ ≤ _; rw [hp,norm_smul,Real.norm_of_nonneg (norm_nonneg _)]; exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans_eq (mul_comm ..)
-- fix interpolation hX via succ +1; no need second derivative equality to fderiv composed only f continuity. Use iterative derivative I.
variable (i:ℕ)
lemma drift (hp:0<t)(h:∀ y∈ closedBall x t,ContDiffAt ℝ ↑(i+2:ℕ) f y)(hX:∀ y∈ closedBall x t, ‖iteratedFDeriv ℝ (i+2) f y‖ ≤M)(he:0 ≤ M)(hY:∀ y∈ closedBall x t, ‖iteratedFDeriv ℝ i f y‖ ≤V) : ‖iteratedFDeriv ℝ (i+1) f x‖ ≤ (V+V)/t+M*t:=by
    let D:= fderiv ℝ (iteratedFDeriv ℝ i f)
    have hd(y: X)(hs:y∈Metric.closedBall x t): DifferentiableAt ℝ (iteratedFDeriv ℝ (i+1) f) y:= (h y hs).differentiableAt_iteratedFDeriv (Nat.cast_lt.2 (by omega))
    rw [← norm_fderiv_iteratedFDeriv]
    refine roam _ hp (fun y hy=> (h y hy).differentiableAt_iteratedFDeriv (Nat.cast_lt.2 (by omega))) (fun y hy=> ?_) (mul_nonneg he hp.le) hY
    have hz := (convex_closedBall x t).norm_image_sub_le_of_norm_fderiv_le hd (fun z h=> (norm_fderiv_iteratedFDeriv).trans_le (hX z h)) (mem_closedBall_self hp.le) hy
    unfold df; rw [fderiv_iteratedFDeriv]; simp only [Function.comp_apply]; rw [← dist_eq_norm]; let a:= continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i+1)=>X) Y; rw [show dist (a _) (a _) = _ from a.isometry.dist_eq (iteratedFDeriv ℝ (i+1) f y) (iteratedFDeriv ℝ (i+1) f x),dist_eq_norm]
    rw[mem_closedBall,dist_eq_norm] at hy; exact hz.trans (mul_le_mul_of_nonneg_left hy he)
open Metric
section
variable (ζ:ℕ→ℝ)(hz:∀ k,1 ≤ζ k)(ht:Tendsto ζ atTop atTop)
-- Set windows carry ambient space. no rates claimed as function of continuation or epoch. polynomially insensitive.
variable (U:Set X)(p:ℕ→X→Y)
noncomputable def rapid (i:ℕ):Prop:=∀ K:Set X,IsCompact K→K ⊆U →∀ (n:ℕ)(ε:ℝ),0<ε →∀ᶠ k:ℕ in atTop,∀ x∈ K, (ζ k)^n * ‖iteratedFDeriv ℝ i (p k) x‖ ≤ ε -- define simp avoid Region
variable (hK:IsOpen U)
variable (gK:∀ k,∀ x∈U,∀ j:ℕ,ContDiffAt ℝ (j:ℕ) (p k) x)(gB:∀ K:Set X,IsCompact K→K ⊆U→∀ j:ℕ,∃ n:ℕ,∃ A:ℝ,0 ≤ A ∧∀ᶠ k in atTop,∀ x∈K, ‖iteratedFDeriv ℝ j (p k) x‖ ≤ A*(ζ k)^n)
include hK gK gB hz ht
lemma here [ProperSpace X] (h:rapid ζ U p 0):∀ i:ℕ, rapid ζ U p i:=by
     intro i; induction i with
     | zero=>exact h
     | succ i ih=>
       intro K hKs hs n ε hε
       obtain ⟨δ,hδ,hΔ⟩:= hKs.exists_cthickening_subset_open hK hs; let S:=Metric.cthickening δ K; have hx:IsCompact S:= hKs.cthickening
       obtain ⟨m,A,hA,H⟩:=gB S hx hΔ (i+2); let d:=n+m+1; let v(k):=(ζ k)^d; let t(k):=(v k)⁻¹
       have ht':Tendsto t atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n:=d) (by omega)).comp ht); have hW:Tendsto (fun k=> A*(ζ k)⁻¹) atTop (𝓝 0):=by simpa only[Function.comp_apply,mul_zero] using ((tendsto_inv_atTop_zero.comp ht).const_mul A)
       filter_upwards [ih S hx hΔ (n+d) (ε/4) (by positivity),H,hW.eventually_le_const (half_pos hε),ht'.eventually_le_const hδ] with k hi hh hp hI x hxl
       let C:= ζ k; let B:= A*C^m; let e':= (ε/4)/C^(n+d); have hC: 0<C:= zero_lt_one.trans_le (hz k); have hj:0 < t k:=inv_pos.mpr (pow_pos hC _)
       have ht : Metric.closedBall x (t k) ⊆ S:=fun z hz=>Metric.mem_cthickening_of_dist_le z x _ _ hxl ((mem_closedBall.mp hz).trans hI)
       have he : ‖iteratedFDeriv ℝ (i+1) (p k) x‖≤ (e'+e')/(t k)+B*t k:= drift (p k) i hj (fun y hy=>gK k _ (hΔ (ht hy)) (i+2)) (fun y hy=> hh y (ht hy)) (show 0 ≤ B from mul_nonneg hA (pow_nonneg hC.le m)) (fun y hy=>by unfold e'; rw[le_div_iff₀ (pow_pos hC _)]; exact mul_comm .. |>.trans_le (hi y (ht hy)))
       apply le_trans (mul_le_mul_of_nonneg_left he (pow_nonneg hC.le n)); change C^n * _≤ ε; rw [mul_add]; have hk:C^n*((e'+e')/ t k)=ε/2:=by unfold e' t v; change _*((_+_)/ (C^d)⁻¹)=_; rw [pow_add]; field_simp; ring
       rw [hk,show C^n*(B*t k)=A*C⁻¹ from ?_]; change A*C⁻¹ ≤ _ at hp; linarith
       unfold B t v; change _*(A*C^m*(C^d)⁻¹)=_; unfold d; rw[pow_succ,pow_add]; field_simp
end
end YM.Sprig.Video
#print axioms YM.Sprig.Video.drift
#print axioms YM.Sprig.Video.here
