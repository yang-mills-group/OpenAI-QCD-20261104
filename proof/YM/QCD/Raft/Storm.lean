import YM.QCD.Raft.Gale

/-! # determinant estimate from inverse and local derivatives at unmasked links -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Cost Push.Uniform Eyrie Stationary Quarry Run Kit Pearl YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace
variable {n:Side} {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T] {D C r:ℝ} (V:T→Sheet n) (h: ContDiffAt ℝ ω V 0) (he:IsUnit (V 0).det)

def presG (V:T→ Sheet n)(x:T):= -Real.log ‖(V x).det‖
include h he
lemma foresaw :
    let M:=fun x:Sheet n=>V 0+x
    let F:= V - fun _=>V 0
    presG V=ᶠ[𝓝 0] fun x=> (-Complex.reCLM (Pearl.actual M (F x))) + presG V 0:=by
  intro M F
  filter_upwards [liftable h he] with x hx
  have ht:M 0=V 0:=add_zero _; have hh:M (F x)=V x:=by unfold M F; rw [Pi.sub_apply]; abel
  change -Real.log _= -(Complex.log _).re + _; rw [ht,hh,Complex.log_re,norm_mul,norm_inv,Real.log_mul (by exact inv_ne_zero (norm_ne_zero_iff.mpr he.ne_zero)) (norm_ne_zero_iff.mpr hx.ne_zero),Real.log_inv]; unfold presG; ring
lemma tollsP : ContDiffAt ℝ ω (presG V) 0 ∧ ∀ x:T,
    Jacobi.mixed x x (presG V) 0=( ( (V 0)⁻¹*blade x V 0*((V 0)⁻¹*blade x V 0)).trace-((V 0)⁻¹*Jacobi.mixed x x V 0).trace).re:=by
  let M:=fun x:Sheet n=> V 0+x
  have hM: AnalyticAt ℂ M 0:= analyticAt_const.add analyticAt_id
  have hx : M 0=V 0:=add_zero _
  have hp : AnalyticAt ℂ (actual M) 0:=actualA hM (hx ▸ he)
  let L: ℂ→L[ℝ] ℝ:= -Complex.reCLM
  let A:=L ∘ (actual M); let F:= V-(fun _=>V 0)
  have hF:F 0=0:=sub_self _; have hu:ContDiffAt ℝ ω F 0:=h.sub contDiffAt_const
  have ht:ContDiffAt ℂ ω (actual M) 0:= hp.contDiffAt
  have hA: ContDiffAt ℝ ω A (F 0):=by rw [hF]; exact L.contDiff.contDiffAt.comp 0 (ht.restrict_scalars ℝ)
  let R:= A∘F; let G:=fun _ :T=> presG V 0
  have hR : ContDiffAt ℝ ω R 0:=hA.comp (f:=F) 0 hu
  have hz: presG V=ᶠ[𝓝 0] R+G:=foresaw V h he; have hS:ContDiffAt ℝ ω (presG V) 0:=(hR.add contDiffAt_const).congr_of_eventuallyEq hz
  refine ⟨hS,fun x=>?_⟩
  have hn : Jacobi.mixed x x G 0=0:=by unfold Jacobi.mixed; rw [show blade x G=(fun _=>0) from funext fun i=> blade_const ..,blade_const]
  rw [repeated x x hz,Eyrie.summed _ _ hR (show ContDiffAt ℝ ω G 0 from contDiffAt_const),hn,add_zero]; unfold R; rw [area_eval _ _ hu hA,hF,retold (f:=actual M) _ _ L (ht.restrict_scalars ℝ), retell _ L (ht.restrict_scalars ℝ)] -- does `blade_over` mixed order?
  have hb : F+(fun _=>V 0)=V:=sub_add_cancel _ _
  have hd: blade x F 0=blade x V 0:=by rw [← show F+(fun _=>V 0)=_ from hb, show blade x (F+(fun _=>V 0)) 0= _ from blade_plus x hu (contDiffAt_const (c:=V 0)), blade_const,add_zero]
  have hl:Jacobi.mixed x x F 0=Jacobi.mixed x x V 0:=by
    have hp : Jacobi.mixed x x (fun _=> V 0) 0=0:=by unfold Jacobi.mixed; rw [show blade x _=(fun i:T=> (0:Sheet n)) from funext fun i=> blade_const x (V 0),blade_const] -- inspect
    rw [← hb]; rw [Eyrie.summed _ _ hu (contDiffAt_const (c:=V 0)), hp,add_zero]
  have hμ x: Pearl.dew x M=(fun _=>x):=by funext i; unfold Pearl.dew M; rw [fderiv_const_add, fderiv_id']; rfl -- inspect
  have hw x: dig x x M 0=0:=by unfold dig; rw [hμ]; exact dew_zero ..
  have hI y: blade y (actual M) 0=dew y (actual M) 0:=by
    unfold blade dew; rw [((ht.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ).fderiv]; rfl
  have h: IsUnit (M 0).det:=hx ▸ he
  have hh : (M 0).det⁻¹*(M 0).det∈Complex.slitPlane:=by rw [inv_mul_cancel₀ h.ne_zero]; exact Or.inl one_pos
  let y:= blade x V 0
  have hO : Jacobi.mixed y y (actual M) 0=Pearl.dig y y (actual M) 0:=by
    rw [iter _ _ (ht.restrict_scalars ℝ),← ((ht.of_le (show (2:WithTop ℕ∞)≤ω from le_top)).restrictScalars_iteratedFDeriv (𝕜:=ℝ) (n:=2))]; change iteratedFDeriv ℂ 2 _ 0 _= _; rw [iteratedFDeriv_two_apply, Pearl.dig_two _ _ hp]; rfl
  rw [hd,hl,hI,dew_actual hM.differentiableAt hh h h]; change L (Jacobi.mixed y y _ _) +_= _; rw [hO, dig_actual hM h y y, hw,hμ,hμ,Matrix.mul_zero,hx]; unfold L y; simp only [Matrix.trace_zero,zero_sub, ContinuousLinearMap.neg_apply,map_neg,Complex.sub_re,Complex.reCLM_apply,neg_neg]; rw [Matrix.mul_assoc (_*_)] ; ring
end YM.QCD.Raft
