import YM.Massive.Quartz.Fee
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Stiffness
-- Cf. `Series.lean`, now for a different gauge-sector fidelity
open Lattice RG Gauge Wilson Pert Pert.Kinetic Precision Function Filter Set
open AnalyticBridge.VerifiedReset Further.LogJets PhysicalNext.Repeat Push Push.AbsoluteSums
open scoped Topology BigOperators ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n c : Side} {ι : Type*} {G : Gauge} {A : ι→ RegularAddress c}{k:ι→ℝ}
  {P: BudgetPoint} {W:ι→ Config G c → ℝ}
section smooth
variable (hG : G.Simple) (hp: ∀ i,P.Regular (A i).support (W i))
    (hk:∀ i,P.supBounds (A i).site (A i).support (W i) (k i))
include hp hk
open Finset
include hG
lemma m_series {δ:ℝ} (he: SumBudget (fun i=> P.mass (A i).support (k i)) ((Fintype.card (Site c):ℝ)*δ)) (g:G.Color) (hx : ‖g‖=1) (hn:4 ≤ c.val) (b:Bool)(i j:Axis) :
   let v : Directions G c := wave g b i j; let F:= fullLog W ∘ AnalyticBridge.VerifiedReset.line v
   ContDiffAt ℝ 2 F 0 ∧ |iteratedDeriv 2 F 0| ≤ Fintype.card (Site c) * (((Full.mesh c)^3*geomE P + (Full.mesh c)^2*(3/P.threshold^2))*δ):=by
   intro v F; have hf:Summable k:= Summable.of_nonneg_of_le (fun i=>(hk i).1) (fun i=>P.loMass _ _ (hk i).1) he.2.1
   refine ⟨(rays_smooth hp hk hf v).of_le (le_trans (by norm_num : (2:WithTop ℕ∞)≤ ((6:ℕ):ℕ∞)) (by exact_mod_cast P.order_ge)),?_⟩
   let a:=(Full.mesh c)^3*geomE P + (Full.mesh c)^2*(3/P.threshold^2); have ha : 0 ≤ a := by unfold a geomE; have hp:=P.threshold_pos; have h1:= P.exponent_pos; have h2:=Full.mesh_pos (n:=c); positivity
   let f(i:ι):=logHessian (W i) v v; have hS:= converge hG hp hk hf v;
   have hg: SumBudget (fun i=> ‖f i‖) (a*((Fintype.card (Site c):ℝ)*δ)):=budget_mono (budget_scale ha he) (fun i=>norm_nonneg _) (fun s=> by
       refine le_trans (Pert.Kinetic.partial_fee g hx b (A s).site (hp s) (A s).anchor (hk s) hn (hG:=hG)) ?_
       unfold a; rw [add_mul]; apply add_le_add_right; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); exact (le_of_eq (by ring : (3:ℝ)*k s/P.threshold^2=3/P.threshold^2*k s)).trans (mul_le_mul_of_nonneg_left (P.loMass _ _ (hk s).1) (by positivity)))
   refine le_trans (b:=‖∑' i,f i‖) ?_ (((norm_tsum_le_tsum_norm hg.2.1).trans hg.2.2).trans_eq ?_)
   · unfold f F; rw [hS.tsum_eq,Real.norm_eq_abs]
   unfold a; ring
end smooth
end YM.Massive.Stiffness

#print axioms YM.Massive.Stiffness.m_series
