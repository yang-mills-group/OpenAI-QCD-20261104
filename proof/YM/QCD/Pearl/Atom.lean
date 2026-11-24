import YM.QCD.Pearl.Blade
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # the exact determinant identity; no exceptional momenta at finite antiperiods -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n : Side} {I J D: Type} {m j : ℕ} {η a b c : ℝ} {L: Momentum}
section calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma hop_cont : ContDiff ℂ ω (Matrix.det (n:=Lat.Row n) (R:=ℂ)):=by
  change ContDiff _ _ (fun X:Sheet n=> Matrix.det X); simp_rw [Matrix.det_apply];
  refine ContDiff.sum (fun σ _=> ContDiff.const_smul _ (contDiff_prod ?_)); intro i _
  let F:Sheet n→ₗ[ℂ] ℂ:={toFun:=fun M=>M (σ i) i,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; exact F.toContinuousLinearMap.contDiff
lemma hop_det {X : Sheet n} (hk:IsUnit X.det) (H : Sheet n):dew H Matrix.det X=X.det*(X⁻¹*H).trace := by
  let f (t:ℂ):= X+t • H
  have he : f 0=X:=by simp[f]
  have hv: HasDerivAt f H 0:=HasDerivAt.const_add X (by simpa using! (hasDerivAt_id' (0:ℂ)).smul_const H)
  have hm : ∀ i j,HasDerivAt (fun t=>f t i j) (H i j) 0:=fun i j=>by
    let F : Sheet n→ₗ[ℂ] ℂ:= { toFun:=fun M=> M i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; exact F.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _ hv
  have ht:= (hop_cont (n:=n)).differentiable (by simp)
  have h':= (ht (f 0)).hasFDerivAt.comp_hasDerivAt 0 hv; have hG:= h'.unique (Cost.jacobi (show IsUnit (f 0).det from he ▸ hk) hm); rw [he] at hG; exact hG

def actual (M:E→Sheet n)(x:E):= Complex.log ((M 0).det⁻¹*(M x).det)
lemma actualA {M:E→Sheet n}(h : AnalyticAt ℂ M 0) (he : IsUnit (M 0).det): AnalyticAt ℂ (actual M) 0:= by
  let g (x:E) := (M 0).det⁻¹*(M x).det
  have hh : AnalyticAt ℂ g 0 := analyticAt_const.mul ((hop_cont (n:=n)).contDiffAt.analyticAt.comp h)
  exact hh.clog (by unfold g; rw [inv_mul_cancel₀ he.ne_zero]; exact Or.inl one_pos)
lemma dew_actual {M:E→Sheet n} {p} (h:DifferentiableAt ℂ M p) (hm:(M 0).det⁻¹*(M p).det∈Complex.slitPlane) (hk:IsUnit (M p).det)(he:IsUnit (M 0).det)(u:E): dew u (actual M) p=((M p)⁻¹ * dew u M p).trace:=by
  let t:= fun z:E=>(M 0).det⁻¹*(M z).det
  have ha : DifferentiableAt ℂ (Matrix.det ∘ M) p:= (hop_cont.differentiable (by simp) (M p)).comp p h
  have ht : DifferentiableAt ℂ t p:=DifferentiableAt.const_mul ha _
  change dew u (Complex.log ∘ t) p=_; rw [dew_chain ht (Complex.differentiableAt_log hm),dew_ℂ, (Complex.hasDerivAt_log hm).deriv]
  rw [show dew u t p = (M 0).det⁻¹ * ((M p).det*((M p)⁻¹*dew u M p).trace) from ?_];
  · simp only [t,smul_eq_mul]; field_simp [he.ne_zero,hk.ne_zero]
  change dew u (fun z=> (M 0).det⁻¹*(Matrix.det ∘ M) z) p=_; rw [dew_mul (differentiableAt_const _) ha,dew_zero,zero_mul,add_zero]
  rw [dew_chain h (hop_cont.differentiable (by simp) _),hop_det hk]
lemma dew_back {M:E→ Sheet n}{x}(hm:DifferentiableAt ℂ M x) (h:IsUnit (M x).det) (u:E):dew u (fun y=>(M y)⁻¹) x= -((M x)⁻¹ * dew u M x * (M x)⁻¹):=by
  let A:=M x; have he:IsUnit A:= A.isUnit_iff_isUnit_det.mpr h -- check
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]; obtain ⟨v,hv⟩:=he
  have ht : M x=(v:Sheet n):=hv.symm
  have hp:= hasFDerivAt_ringInverse (𝕜:=ℂ) v
  change dew u (Ring.inverse ∘ M) x=_; rw [dew_chain hm (show DifferentiableAt ℂ _ _ from ht.symm ▸ hp.differentiableAt),ht,Ring.inverse_unit];
  change fderiv ℂ Ring.inverse (v:Sheet n) _= _
  rw [hp.fderiv]; rfl
lemma dig_actual {M:E→Sheet n}(h : AnalyticAt ℂ M 0) (he : IsUnit (M 0).det)(u v:E): dig u v (actual M) 0=
    ((M 0)⁻¹*dig u v M 0).trace - ((M 0)⁻¹*dew u M 0*(M 0)⁻¹*dew v M 0).trace:=by
  let U:E→Sheet n:=fun x=> (M x)⁻¹
  have hu : (dew v (actual M)) =ᶠ[𝓝 0] fun x=> (U x*dew v M x).trace:=by
    let t:= fun z:E=>(M 0).det⁻¹*(M z).det
    have ht : AnalyticAt ℂ t 0 := analyticAt_const.mul ((hop_cont (n:=n)).contDiffAt.analyticAt.comp h)
    have ht1 : t 0=1:=inv_mul_cancel₀ he.ne_zero
    have he' := Complex.isOpen_slitPlane
    filter_upwards [ht.continuousAt.eventually (he'.mem_nhds (show t 0∈Complex.slitPlane by rw [ht1]; exact Or.inl one_pos)), h.eventually_analyticAt, ((hop_cont (n:=n)).contDiffAt.analyticAt.comp h).continuousAt.eventually_ne he.ne_zero] with i hi hr hq; exact dew_actual hr.differentiableAt hi (IsUnit.mk0 _ hq) he v
  unfold dig; rw [dew_var hu]
  let T: Sheet n→L[ℂ] ℂ:=(Matrix.traceLinearMap (Lat.Row n) ℂ ℂ).toContinuousLinearMap
  have hvx:DifferentiableAt ℂ U 0:=by
    unfold U; simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    apply DifferentiableAt.comp (g:=Ring.inverse) (f:=M) (x:=0) _ h.differentiableAt
    obtain ⟨k,hk⟩:=(M 0).isUnit_iff_isUnit_det.mpr he; rw [← hk]; exact (hasFDerivAt_ringInverse _).differentiableAt
  rw [show (fun x=> (U x*dew v M x).trace)= T ∘ fun x=>U x*dew v M x from rfl, dew_chain (hvx.fun_mul (voiced v h)) T.differentiableAt,dewp] -- fix
  rw [dew_mul hvx (voiced v h),show dew u U 0= _ from dew_back h.differentiableAt he u,neg_mul, map_add,map_neg]; rfl
end calculus
end YM.QCD.Pearl
