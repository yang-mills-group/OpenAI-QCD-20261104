import YM.Rill.Zone
/-! Power law uniform width. Mass seam normalization etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q: Choir}(L:Pollens P Q)(a:Axis)
variable (p:Strip Q)(d r:ℝ)(D I:ℕ) (hr:0<r)(hd:0 ≤ d)
variable (G:∀ d,Cottage P d)(hS:Sway C.S) {β e:ℝ}(hp:C.Path β e) {φ:ℕ→ℕ} (H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop) (hP:P.System)
private lemma weights (d:ℕ) (f: Label d≃ₛₗ[starRingEnd ℂ]Label d):∃ T:ℝ,0 ≤ T ∧∀ p, ‖f p‖ ≤ T*‖p‖:=by
     let B:= Fir.lid d; let X(i):= (B.coord i).toContinuousLinearMap; let W(i):= ‖X i‖*‖f (B i)‖; refine ⟨∑ i,W i,sum_nonneg (fun _ _=> mul_nonneg (norm_nonneg _) (norm_nonneg _)),fun p=>?_⟩; nth_rw 1 [← B.sum_repr p]; rw [map_sum,sum_mul]; apply (norm_sum_le ..).trans; refine sum_le_sum fun i _=>?_ ; rw [map_smulₛₗ,norm_smul]; simp only [starRingEnd_apply,norm_star]; exact (mul_le_mul_of_nonneg_right ((X i).le_opNorm p) (norm_nonneg _)).trans_eq (by unfold W; ring)
include G hp H hS
lemma chargedF : ∃ m:ℕ,∃ V:ℝ,1 ≤ V∧∀ r:ℝ,0< r → r ≤ 1 →∃ j:ℕ,C.S.spacing j < r/16∧ I*16<(C.S.step j).L.val ∧∀ p: Q.level D, ‖p‖≤1 → Privilege P Q j p.val (V*r⁻¹^m) ∧Privilege P Q j (L.adj a p.val) (V*r⁻¹^m):=by
     let X:= Q.level D; let U:=(Q.focus none D).rangeRestrict; obtain ⟨F,hF⟩:= U.exists_rightInverse_of_surjective ((Q.focus none D).range_rangeRestrict) -- U of rangeRestrict has `.range_rangeRestrict` for its own further; fix
     let Z:= F.toContinuousLinearMap; let T:= P.sym.adj D a; have he(u:X): Q.focus none D (F u)=u.val:= congr_arg Subtype.val (DFunLike.congr_fun hF u); let K:= (G D).rise
     obtain ⟨N,hN⟩:=eventually_atTop.mp (K.nest.and (hS.high.eventually_gt_atTop (I*16))); -- need T norm. semilinear
     obtain ⟨t,ht,h'T⟩:= weights D T; let v:= max ‖Z‖ (t * ‖Z‖); have hv:0 ≤ v:=(norm_nonneg Z).trans (le_max_left ..); let k:ℝ:= (D:ℝ)/2+1; have hk:0 ≤ k:=by unfold k; positivity
     obtain ⟨m,A,hA,h⟩:= ticking hp hS N (v*K.v) k (mul_nonneg hv K.green) hk; let W:=max 1 (A*16^m); have hW:1≤W:= le_max_left ..; refine ⟨m,W,hW,fun r hr hx=>?_⟩; obtain ⟨j,hj,hL,hX⟩:= h (r/16) (by positivity) (by linarith); let R:=W*r⁻¹^m
     have hy (w:Label D)(hq:‖w‖ ≤ v): Privilege P Q j (Q.focus none D w) R:=by
           refine ⟨D,w,rfl,?_⟩; filter_upwards [(hN j hj).1] with i hi; apply GreenP.mono (hi w); refine (mul_le_mul_of_nonneg_right hq (K.power j)).trans ?_; unfold rayM; rw[←mul_assoc]; apply hX.trans; unfold R; rw [show (r/16)⁻¹=16*r⁻¹ from by field_simp, mul_pow,←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
     refine ⟨j,hL,(hN _ hj).2,fun p hq=>?_⟩; have hz: ‖Z p‖ ≤ ‖Z‖:= (Z.le_opNorm p).trans (mul_le_of_le_one_right (norm_nonneg _) hq); have h:= hy (F p) (hz.trans (le_max_left ..)); refine ⟨he p ▸ h,?_ ⟩; rw [← he p,L.a]; exact hy _ ((h'T (F p)).trans ((mul_le_mul_of_nonneg_left hz ht).trans (le_max_right ..)))
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.chargedF
