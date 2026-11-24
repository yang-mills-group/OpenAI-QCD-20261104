import YM.Massive.Stiffness.Main
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Ghost

/-!
# Series of regular E-pieces differentiated on these same real representatives
(need no separate E estimate at the origin in the trivial sector's cofinal mesh).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Stiffness
open Lattice RG Gauge Wilson Pert Pert.Kinetic Precision Function Filter Set
open AnalyticBridge.VerifiedReset Further.LogJets PhysicalNext.Repeat Push Push.AbsoluteSums
open scoped Topology BigOperators ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n c : Side} {ι : Type*} {G : Gauge} {A : ι→ RegularAddress c}{k:ι→ℝ}
  {P: BudgetPoint} {W:ι→ Config G c → ℝ}
open Finset in
lemma encloses_gauge (hp: ∀ i,P.Regular (A i).support (W i)) (hf: Summable k) (hk: ∀ i,P.supBounds (A i).site (A i).support (W i) (k i)) : Termwise P.order (Boulevard.sunny P) W:= by
  have he i (x:Config G c) (hx:x∈Boulevard.sunny P): Healthy P.threshold (A i).support x:= by unfold Healthy; rw [Boulevard.smoky hx]; simp
  refine ⟨fun i x hx=>(hp i).smooth _ (he i x hx),fun l hl=>?_⟩
  let d:= P.threshold+l.toFinset.sum (fun i=> ‖i‖)
  have hd : 0<d:= add_pos_of_pos_of_nonneg P.threshold_pos (sum_nonneg fun i _=> norm_nonneg _)
  have hu : ∀ i∈l, ‖i‖≤d:= fun i hi=> (single_le_sum (fun a _=> norm_nonneg a) (List.mem_toFinset.mpr hi)).trans (le_add_of_nonneg_left P.threshold_pos.le)
  let b:=d/P.threshold; have hb: 0<b:= div_pos hd P.threshold_pos; let Y:=l.map fun i=> b⁻¹ • i
  have hY:Y.length=l.length:= by simp [Y]
  have ht : Y.map (fun i=>b • i)=l:= by simp [Y,List.map_map,Function.comp_def,smul_smul,hb.ne']
  have hh i : ∀ j∈Y,P.dirBound (A i).site j:= by
    intro j hj; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hj; apply Boulevard.tiny
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hb).le]; apply le_trans (mul_le_mul_of_nonneg_left (hu _ ha) (inv_nonneg.mpr hb.le)); apply le_of_eq; unfold b; field_simp
  refine ⟨fun i=>b^Y.length*k i,hf.mul_left _,fun i x hx=> ?_⟩; rw [← ht, ConnectedActivityE6.Blaze.March.expands,norm_smul,Real.norm_of_nonneg (pow_pos hb _).le]
  exact mul_le_mul_of_nonneg_left ((hk _).2 x (he i x hx) Y (hY ▸ hl) (hh i)) (pow_nonneg hb.le _)

def fullLog (W:ι→ Config G c→ℝ) (V : Config G c):=∑' i,W i V

section smooth
variable (hG : G.Simple) (hp: ∀ i,P.Regular (A i).support (W i))
    (hk:∀ i,P.supBounds (A i).site (A i).support (W i) (k i))
include hp hk
lemma rays_smooth (hf: Summable k) (v : Directions G c) :
    ContDiffAt ℝ (P.order:ℕ∞) (fullLog W ∘ AnalyticBridge.VerifiedReset.line v) 0:=by
   have hx : (1:Config G c)∈ Boulevard.sunny P:=fun i=> by rw [WilsonStartup.face_one, G.chord_one]; exact P.threshold_pos -- defeq?
   have he : ContDiffAt ℝ (P.order:ℕ∞) (fullLog W ∘ increment 1) 0:=(Termwise.smooth_exchange (Boulevard.sky P) (encloses_gauge hp hf hk) 1 hx).1
   have hz : (0:ℝ) • v=0:=zero_smul ..
   exact (show ContDiffAt ℝ (P.order:ℕ∞) (fullLog W ∘ increment 1) ((0:ℝ) • v) from hz.symm ▸ he).comp (f:=fun t:ℝ=> t • v) 0 (by fun_prop)

include hG
open Finset in
lemma converge (hf:Summable k) (v : Directions G c) : HasSum (fun i=>logHessian (W i) v v) (iteratedDeriv 2 (fullLog W ∘ AnalyticBridge.VerifiedReset.line v) 0):=by
   have hx : (1:Config G c)∈ Boulevard.sunny P:=fun i=> by rw [WilsonStartup.face_one, G.chord_one]; exact P.threshold_pos
   have hl : [v,v].length ≤ P.order:= (by have ht:= P.order_ge; simp; omega)
   have hh := Next.Foundations.leftDerivs_diag (1:Config G c) v (fullLog W) 2 0; rw [zero_smul,at_zero] at hh; let u:= (encloses_gauge hp hf hk)
   simp_rw [hessian_diag hG (hp _)]; change HasSum _ (iteratedDeriv 2 (fun x:ℝ=> fullLog W (increment 1 (x • v))) 0); rw [← hh]; change HasSum _ (leftDerivs (fun V=> ∑' i, W i V) [v,v] 1); rw [(Termwise.smooth_exchange (Boulevard.sky P) u 1 hx).2 _ hl]; exact (u.sums [v,v] hl 1 hx).hasSum

variable (h :∀ i, Nonwrapping (A i).support (A i).site → ∀ a b,IsAffineDirection (A i).site a → IsAffineDirection (A i).site b → logHessian (W i) a b=0)
include h
lemma series {δ:ℝ} (he: SumBudget (fun i=> P.mass (A i).support (k i)) ((Fintype.card (Site c):ℝ)*δ)) (g:G.Color) (hx : ‖g‖=1) (hn:4 ≤ c.val) (b:Bool)(i j:Axis) :
   let v : Directions G c := wave g b i j; let F:= fullLog W ∘ AnalyticBridge.VerifiedReset.line v
   ContDiffAt ℝ 2 F 0 ∧ |iteratedDeriv 2 F 0| ≤ Fintype.card (Site c) * ((Full.mesh c)^3*geomE P*δ):=by
   intro v F; have hf:Summable k:= Summable.of_nonneg_of_le (fun i=>(hk i).1) (fun i=>P.loMass _ _ (hk i).1) he.2.1
   refine ⟨(rays_smooth hp hk hf v).of_le (le_trans (by norm_num : (2:WithTop ℕ∞)≤ ((6:ℕ):ℕ∞)) (by exact_mod_cast P.order_ge)),?_⟩
   let a:=(Full.mesh c)^3*geomE P; have ha : 0 ≤ a := by unfold a geomE; have hp:=P.threshold_pos; have h1:= P.exponent_pos; have h2:=Full.mesh_pos (n:=c); positivity
   let f(i:ι):=logHessian (W i) v v; have hS:= converge hG hp hk hf v; have hg: SumBudget (fun i=> ‖f i‖) (a*((Fintype.card (Site c):ℝ)*δ)):=budget_mono (budget_scale ha he) (fun i=>norm_nonneg _) (fun s=> one_fee g hx b (A s).site (hp s) (A s).anchor (hk s) (h s) hn (hG:=hG))
   refine le_trans (b:=‖∑' i,f i‖) ?_ (((norm_tsum_le_tsum_norm hg.2.1).trans hg.2.2).trans_eq ?_)
   · unfold f F; rw [hS.tsum_eq,Real.norm_eq_abs]
   unfold a; ring
end smooth
end YM.Massive.Stiffness
#print axioms YM.Massive.Stiffness.series
