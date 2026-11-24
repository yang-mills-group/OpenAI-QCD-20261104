import YM.QCD.Raft.Intercept

/-! # vanish extra moment. orientation in Grad bound -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Bid Eyrie Stationary Quarry Work.F03 Exterior Matrix YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {n:Side}{η C:ℝ}
def speedL (n:Side):= q (strandT (Pearl.beamH n)) 0
lemma track_limit : Tendsto (fun n=> (Pearl.beamH n:ℝ)⁻¹ • speedL n) atTop (𝓝 Complex.I):=by
  let f(t:ℝ):= Complex.exp (Complex.I*(t:ℂ))-1
  have hd: HasDerivAt (fun t:ℂ=> Complex.exp (Complex.I*t)-1) Complex.I 0:=by simpa using! (((hasDerivAt_id' (0:ℂ)).const_mul Complex.I).cexp.sub_const 1)
  have he: HasDerivAt f Complex.I 0:=by
    let L:= Complex.ofRealCLM; have ht : HasDerivAt (fun x:ℝ=> (x:ℂ)) 1 0 := L.hasFDerivAt.hasDerivAt
    -- chain over CLM restrict
    have h := hd.hasFDerivAt.restrictScalars ℝ; convert! h.comp_hasDerivAt (f:=fun r:ℝ=>(r:ℂ)) (x:=(0:ℝ)) ht using 1 <;> simp -- inspect
  have hm : f 0=0:=by simp[f]
  have hx : ∀ n, speedL n=f (Pearl.beamH n):=fun n=>by simp [speedL,f,q,strandT]
  simp_rw [hx]; refine ((hasDerivAt_iff_tendsto_slope.mp he).comp (tendsto_nhdsWithin_iff.mpr ⟨Pearl.beam0,Eventually.of_forall fun i=>(Pearl.beamP _).ne'⟩)).congr' (Eventually.of_forall fun i=>by simp [Function.comp_apply,slope_def_module,hm])
lemma speeds : Tendsto speedL atTop (𝓝 0):=by
  have he:= Pearl.beam0.smul track_limit; rw [zero_smul] at he; apply he.congr'; exact Eventually.of_forall fun i=> by change Pearl.beamH i • ((Pearl.beamH i)⁻¹ • speedL i)=_; rw [smul_smul,mul_inv_cancel₀ (Pearl.beamP i).ne',one_smul]
lemma metric_limit (T:Bed)(a:su.Color)(hp:T.metric.strip η C)(hu:0<η)(he:T.metric.read 0=1)(ha:‖a‖=1): Tendsto (fun n=> let X:=arm su n 1 (poke a n).1; let Y:=arm su n 1 (poke a n).2; (gaugeFiscal T X X+ gaugeFiscal T Y Y)/densityP n) atTop (𝓝 1):=by
  let B p:=(T.metric.read p (plaquette keyP) (plaquette keyP)).re
  have ht: ContDiffAt ℝ ω B 0:= Complex.reCLM.contDiff.contDiffAt.comp (f:=fun p=>T.metric.read p (plaquette keyP) (plaquette keyP)) 0 (smear ((Push.Loops.row_analytic hp hu (show (0:Momentum)∈_ from by intro i; simp; linarith)).restrict_scalars ℝ) _ _)
  have hh:B 0=1:=by unfold B; rw [he,one_apply_eq]; rfl
  have hb : Tendsto (fun p=> B (strandT (Pearl.beamH p))) atTop (𝓝 1):=by
    rw [← hh]; apply ht.continuousAt.tendsto.comp; rw [← show strandT 0=0 from by simp[strandT]]; exact (show Continuous strandT from Complex.ofRealCLM.continuous.smul continuous_const).continuousAt.tendsto.comp Pearl.beam0 -- inspect
  have hT:= (track_limit.norm.pow 2).mul hb; rw [Complex.norm_I, one_pow,one_mul] at hT
  apply hT.congr'; refine Eventually.of_forall fun n=> ?_; dsimp only; rw [show (Bid.gaugeFiscal T _ _ + _) = _ from inkG (n:=n) T a hp hu ha]; simp only [norm_smul,norm_inv]; let d:= Pearl.beamH n
  have hv:0<d:= Pearl.beamP _
  change _*(B _)=(cap _*‖speedL n‖^2 * B _)/_; rw [Real.norm_of_nonneg hv.le]; unfold densityP; field_simp [(cap_pos _).ne', (Pearl.beamP _).ne']; unfold d; ring

lemma exp_swing (i:Axis)(x:Site n): ‖cell (step 0) (x+step i)-cell (step 0) x‖≤ ‖speedL n‖ :=by
  let Q:= cell (step 0: Site n) x
  rw [cell_add,show Q*_-Q=Q*(cell (step 0:Site n) (step i)-1) from ?_]; swap; · unfold Q; ring
  by_cases h:i=0; · subst i; rw [norm_mul,show ‖Q‖=1 from mode_real _ _ (real_frequency _),one_mul,(residentQ n).step]; exact le_rfl
  rw [cellG _ h,sub_self,mul_zero,norm_zero]; exact norm_nonneg _
lemma volition (x y:Site n)(he: ∃ a:Axis,x+step a=y ∨ y+step a=x) (p:TypeFace 2):
    ‖vw (step 0) (melody (Pearl.beamH n)) (y,p)-vw (step 0) (melody (Pearl.beamH n)) (x,p)‖ ≤ ‖speedL n‖^2:=by
  have ht : ‖cell (step 0) y-cell (step 0) x‖≤‖speedL n‖:=by
    obtain ⟨b,h|h⟩:=he; · rw [← h]; exact exp_swing b x
    rw [← h,norm_sub_rev]; exact exp_swing b y
  unfold vw; dsimp only; rw [← sub_mul, norm_mul,sq]; apply mul_le_mul ht _ (norm_nonneg _) (norm_nonneg _); unfold melody; by_cases h:p=plaquette keyP; · subst p; simp[speedL]
  rw [Pi.single_eq_of_ne h,norm_zero]; exact norm_nonneg _
