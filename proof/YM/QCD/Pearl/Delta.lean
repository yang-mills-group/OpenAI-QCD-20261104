import YM.QCD.Rudder.Spout

/-! # complex directional germs and their summed costs -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Finset Function Filter Metric Lat Rudder
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] {f g:E→F} {x u v : E} {I:Type*}

def dew (u : E) (f : E→ F)(x:E):= fderiv ℂ f x u
def dig (u v : E) (f : E→ F):= dew u (dew v f)
lemma dewp (F:E→L[ℂ] G)(x u:E):dew u F x=F u:=by unfold dew; rw [ContinuousLinearMap.fderiv]
lemma dew_ℂ {f:ℂ→E}{z w : ℂ}: dew w f z=w • deriv f z:=by unfold dew deriv; nth_rw 1 [show w=w • (1:ℂ) from ((smul_eq_mul ..).trans (mul_one w)).symm]; rw [map_smul]
lemma dew_zero (C : F) (x u:E):dew u (fun _=>C) x=0:=by simp [dew]
lemma dew_plus (hf:DifferentiableAt ℂ f x)(hg:DifferentiableAt ℂ g x) (v:E):dew v (f+g) x=dew v f x+dew v g x:=by unfold dew; rw [fderiv_add hf hg]; rfl
lemma dew_chain {g:F→G} (hf:DifferentiableAt ℂ f x)(hg:DifferentiableAt ℂ g (f x))(v:E):dew v (g ∘ f) x=dew (dew v f x) g (f x):=by unfold dew; rw [fderiv_comp _ hg hf]; rfl
lemma dew_s {w : E→ℂ}(h:DifferentiableAt ℂ w x)(hg:DifferentiableAt ℂ g x)(v:E):dew v (fun z=> w z • g z) x=w x • dew v g x+dew v w x • g x:=by
  unfold dew; rw [fderiv_fun_smul h hg]; rfl
lemma voiced [CompleteSpace F] (v:E)(h : AnalyticAt ℂ f x) : DifferentiableAt ℂ (dew v f) x:= by
  have hf := h.contDiffAt (n:=ω)
  exact ((hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).clm_apply (differentiableAt_const _)
variable {R: Type*} [NormedRing R] [NormedAlgebra ℂ R] {p q:E→R}
lemma dew_mul (h:DifferentiableAt ℂ p x)(hq:DifferentiableAt ℂ q x)(v:E): dew v (fun i=>p i*q i) x=p x * dew v q x+dew v p x*q x:=by unfold dew; rw [fderiv_fun_mul' h hq]; rfl
section finite
variable [FiniteDimensional ℂ E] -- F assumptions chained
lemma drip_prod [FiniteDimensional ℂ R] (hp:Differentiable ℂ p)(hq:Differentiable ℂ q)(x u v:E):dig u v (fun i=>p i*q i) x=(p x*dig u v q x+dew u p x *dew v q x)+(dew v p x*dew u q x+dig u v p x * q x):=by
  haveI:=FiniteDimensional.complete ℂ R
  unfold dig; rw [show dew v (fun i=>p i*q i)=(fun i=>p i*dew v q i)+(fun i=> dew v p i*q i) from funext (fun i=> dew_mul (hp i) (hq i) _)]
  have ht:= voiced v (PolyDisc.finiteD p (x:=x) (Eventually.of_forall hp)); have hh:= voiced v (PolyDisc.finiteD q (x:=x) (Eventually.of_forall hq)); rw [dew_plus ((hp x).fun_mul hh) (ht.fun_mul (hq x)),dew_mul (hp x) hh,dew_mul ht (hq x)]
end finite
lemma dew_var (h : f =ᶠ[𝓝 x] g) (u:E):dew u f x=dew u g x:=by unfold dew; rw [h.fderiv_eq]
lemma dig_two [CompleteSpace F] (u v : E) (h : AnalyticAt ℂ f x): dig u v f x= (fderiv ℂ (fderiv ℂ f) x u) v:= by
  let T:= ContinuousLinearMap.apply ℂ F v; have hp : dew v f=T ∘ fderiv ℂ f:=rfl
  have he:= (h.contDiffAt (n:=ω)).fderiv_right (m:=ω) (by simp) |>.differentiableAt (by simp)
  rw [dig,hp,dew_chain he T.differentiableAt,dewp]; rfl
section series
variable {α : ℝ}
omit [NormedAddCommGroup F] [NormedSpace ℂ F] in
lemma internal_drop [CompleteSpace G] (f:I→ E→G)(u:E) (h : 0<α)(hf : ∀ i, Differentiable ℂ (f i)) {p:I→ℝ} (hp : Summable p)
    (hu : ∀ i z,z∈ball (0:E) α → ‖f i z‖ ≤ p i)(y:E)(hy:y∈ball 0 (α/2)): HasSum (fun i=> dew u (f i) y) (dew u (fun z=>∑' i,f i z) y) := by
  letI : NormedSpace ℝ E:=NormedSpace.restrictScalars ℝ ℂ E
  let S:=ball (0:E) (α/2)
  have he := hp.div_const (α/2)
  have hw i (x) (hx:x∈S): ‖fderiv ℂ (f i) x‖ ≤ p i/(α/2):= Work.F02.fderiv_bound (hf i) h (hu i) hx
  have hD: HasFDerivAt (fun z=>∑' i,f i z) (∑' i,fderiv ℂ (f i) y) y := hasFDerivAt_tsum_of_isPreconnected he isOpen_ball (convex_ball (0:E) _).isPreconnected (fun i x _=> (hf i x).hasFDerivAt) hw (mem_ball_self (half_pos h)) (hp.of_norm_bounded (fun i=> hu i 0 (mem_ball_self h))) hy
  unfold dew; rw [hD.fderiv]
  exact (ContinuousLinearMap.apply ℂ G u).hasSum (he.of_norm_bounded (fun i=> hw i y hy)).hasSum
lemma external_drop [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (f:I→ E→F)(u v:E) (h : 0<α)(hf : ∀ i,Differentiable ℂ (f i)) {p:I→ℝ} (hp : Summable p)
    (hu : ∀ i z,z∈ball (0:E) α→‖f i z‖ ≤ p i): HasSum (fun i=>dig u v (f i) 0) (dig u v (fun z=>∑' i,f i z) 0):=by
  haveI:=FiniteDimensional.complete ℂ F
  let g i:= dew v (f i); have ht:= hp.div_const (α/2)
  have hs (i) : Differentiable ℂ (g i) := fun _=> voiced v (PolyDisc.finiteD (f i) (Eventually.of_forall (hf i)))
  have he i x (hx:x∈ball (0:E) (α/2)) : ‖g i x‖ ≤ p i/(α/2)*‖v‖:= (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right (Work.F02.fderiv_bound (hf i) h (hu i) hx) (norm_nonneg v))
  unfold dig; rw [dew_var (g:=fun z=>∑' i,g i z)]; exact internal_drop g u (half_pos h) hs (ht.mul_right ‖v‖) he 0 (mem_ball_self (by positivity))
  filter_upwards [ball_mem_nhds (0:E) (half_pos h)] with y hy; exact (internal_drop f v h hf hp hu y hy).tsum_eq.symm
end series
end YM.QCD.Pearl
