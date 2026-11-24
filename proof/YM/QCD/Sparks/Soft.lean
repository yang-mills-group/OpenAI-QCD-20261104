import YM.QCD.Sparks.Flair

/-!
# Actual curvature-form row expansion on every period of the chain. Across not
just the subsequence or subsequent renormalization points. `plain` too (for H traces)
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Run
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable (S:SparkMesh) {r C:ℝ} {p k: ℕ} {m:ℕ→ℕ} {F:S.Field} {K : Typewriter k}
    (h:Clan S F) (H: Exhibit S F k r C m K) (hc:0≤C) (hr:0<r)
include h H hc hr
local notation "n" => S.n p
local notation "N[" i "]" => S.n (m i)
lemma plain (x: Fin k→ Cnr n)(y : Site n): Run.cell (surge (F p) x) 0 y=∑' q:Tilt k, if wrap n q.1=y then
    (∏ i,x i (wrap n (q.2 i).1,(q.2 i).2)) • (occ (0:Site n) q.1 • K q) else 0:=by
  let B (q:ℕ) : Fin k→ Cnr N[q] := if h : p ≤ m q then expandC (S.vista p (m q) h)∘x else 0
  have hb := H.climbs.tendsto_atTop.eventually_ge_atTop p
  refine directed S p x h H hc hr y B (fun a i => x i (wrap n a.1,a.2)) ‖x‖ (norm_nonneg _) ?_ ?_ ?_
  · intro q h'; unfold B; rw [dif_pos h']
  · intro l i; apply tendsto_const_nhds.congr'
    filter_upwards [hb] with q h; unfold B; rw [dif_pos h, Function.comp_apply,repin]; dsimp only; rw [passThrough]
  filter_upwards [hb] with q h' z i; unfold B; rw [dif_pos h', Function.comp_apply,repin]; refine ((norm_le_pi_norm (x i) _).trans (norm_le_pi_norm x i)).trans (le_mul_of_one_le_right (norm_nonneg _) (le_add_of_nonneg_right (by positivity))) -- positivity ge?
lemma lyrical (x:Fin k→ Cnr n)(y: Site n)(he : ∀ j,EmptyThrough (F j) k) (hk:k≤2):
    Run.cell (surge (F p) x) 0 y=∑' q:Tilt k, if wrap n q.1=y then (∏ i, idyllic (q.2 i) (x i)) • (occ (0:Site n) q.1 • K q) else 0:=by
  let B (q:ℕ)(i:Fin k): Cnr N[q]:= if h:p≤m q then pacify (S.vista p (m q) h) (x i) else 0
  have hb:= H.climbs.tendsto_atTop.eventually_ge_atTop p
  let T:=16*‖x‖
  refine directed S p x h H hc hr y B (fun a i=> idyllic a (x i)) T (by unfold T; positivity) ?_ ?_ ?_
  · intro p' hp; unfold B; simp_rw [dif_pos hp]; exact paidWard (h.way _) (he _) hk (fun i=>limitAt (x i) N[p']) _
  · intro w i; apply tendsto_const_nhds.congr'
    filter_upwards [hb,chargeNext S H.climbs w.1,chargeNext S H.climbs (w.1+step (axisEquiv.symm w.2.1))] with q hp hv hm; unfold B; rw [dif_pos hp]; exact (isp _ (x i) w (into ..) hv hm).symm
  filter_upwards [hb] with q h z i; unfold B; rw [dif_pos h]; apply (spend_axis _ (x i) z).trans
  rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (by norm_num)) (by positivity)
end YM.QCD.Sparks
