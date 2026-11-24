import YM.QCD.Pearl.Stir
import YM.QCD.Free.Ray

/-! # no anomalous speed coefficient. recover precisely V at zero by Seq pins -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n:Side}{I J D:Type}{p:Site n}{j : ℕ}{G:I→Gleam}{U:J→Bloom 1}{V:D→Bloom 2}{P:Plan j}{v:Train j}{η a b c:ℝ}(C : su.Color)

def prog (G:I→Gleam)(p:Momentum):=∑' i, boom (G i) p
lemma miracle (Q:Gleam):Differentiable ℂ (boom Q):= (wane_d Q.w).mul_const _
lemma zoom (h:Package η a b c P v G U V)(p : Site n):prog G (tuning p)=model (Dir v (tuning p)):=by
  let g: I→Sheet n:=fun i=> (G i).dept 0 1
  have he : peel (wood P 0 v (1:Grid n))=lined fun k=>prog G (tuning k):=by
    apply billBeam g (fun i k=> boom (G i) (tuning k)) _ (h.matchA ..); intro i; unfold g Gleam.dept; rw [peel_mul,unroll 0 _ p,peel_spin,lined_law]; rfl
  rw [bare_this,unbarred,carries] at he
  ext a b; replace he := congr_fun (congr_fun he (p,a)) (p,b); simp only [lined,rr,Equiv.refl_apply,if_true,rangeD] at he; exact he.symm
lemma gle (w:Walk)(a:Axis): glitter w 0 a=(stop (0:Cover) w a:ℤ):=by
  have ht (w:Walk)(x:Cover): bill (flash 0 a) x w= ((↑(stop x w a-x a):ℤ):ℂ):=by
    induction w generalizing x with
    | nil=> simp [stop,bill]
    | cons i w ih=> rw [bill,stop,ih]; rcases i with ⟨i,_|_⟩ <;> by_cases hv:a=i <;> simp [Step.used,Step.vec,flash,hv] <;> ring
  rw [glitter,ht]; simp
lemma hack0 (w:Slot)(a:Axis): hack w 0 a=0:=by -- closed
  unfold hack; simp [flash,bill,Lattice.square,posDir,negDir,Step.used]
lemma progFirst (a:Axis)(Q:Gleam):dew (step a) (boom Q) 0=(Complex.I*glitter Q.w 0 a) • boom Q 0:=by
  let X:=stop (0:Cover) Q.w
  have hp : dew (step a) (fun p:Momentum=>mode p X) 0=Complex.I*glitter Q.w 0 a:=by
    have hm: Differentiable ℂ (fun p:Momentum=>mode p X):=by unfold mode; fun_prop
    let L:ℂ→L[ℂ] Momentum:= ContinuousLinearMap.toSpanSingleton ℂ (step a : Momentum)
    have he (t:ℂ): L t=t • step a:=rfl
    have ht:= dew_chain L.differentiableAt (hm (L 0)) (1:ℂ)
    have hh : (fun p=> mode p X) ∘ L=fun t=> Complex.exp (t*(Complex.I*(X a:ℂ))):=by
      funext t; unfold mode; rw [comp_apply,he]; simp only [Pi.smul_apply,smul_eq_mul]; rw [sum_eq_single a]; simp; ring
      · intro i _ hv; simp [hv]
      simp
    rw [hh,dew_ℂ,dewp,map_zero, he 1,one_smul,one_smul] at ht; change _=_ at ht
    rw [← show deriv (fun t:ℂ=> Complex.exp (t*(Complex.I*(X a:ℂ)))) 0=dew (step a) (fun p:Momentum=>mode p X) 0 from ht]
    rw [gle]; simpa [X] using (((hasDerivAt_id' (0:ℂ)).mul_const (Complex.I*(X a:ℂ))).cexp).deriv
  change dew _ (fun p=> wane p Q.w * _) _=_; rw [dew_mul_const' (wane_d _)]; unfold wane; rw [dew_tw _ _ _ _ _, hp]; simp [boom,wane,Matrix.smul_mul,oneNorm]
  unfold mode; fun_prop
lemma boom_jet (i:Axis)(W:Gleam): boom₁ C W i 0 0 = (-Complex.I) • (touch (echo C)*dew (step i) (boom W) 0):=by unfold boom₁; rw [progFirst,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← mul_assoc (-Complex.I),neg_mul,Complex.I_mul_I,neg_neg,one_mul]
lemma prog_demand (h:Package η a b c P v G U V)(u : Momentum):DifferentiableAt ℂ (prog G) 0∧ HasSum (fun i=>dew u (boom (G i)) 0) (dew u (prog G) 0) := by
  obtain ⟨r,hr,H⟩:= hill (0:su.Color) h.scale
  have he:= cube_zero (η/2) (half_pos h.scale)
  have hy:(0:Momentum)∈ strip η := (cube_zero η h.scale).1
  have hp:= ball_inside_cube (η:=η) he
  have hh:=h.psi.val.mul_left r
  have hu i q (hq:q∈ball (0:Momentum) (η-η/2)):‖boom (G i) q‖≤ _ := (H (G i) 0 q hy (hp hq).1 0).1
  have hd : 0<η-η/2:=by linarith [h.scale]
  exact ⟨(Work.F02.analytic_series _ hd (fun i=> miracle _) hh hu).differentiableAt,internal_drop _ u hd (fun i=> miracle _) hh hu 0 (mem_ball_self (half_pos hd))⟩

def trackV (x: Cover): Momentum:= fun i=> (fixed x i:ℂ)
def trek (n : Side): ℂ:= ((n.val:ℝ)⁻¹:ℝ)
lemma advance_0 : Tendsto trek atTop (𝓝[≠] 0):=by
  have he: Tendsto spacer atTop (𝓝 0):= shrinks.mono_right nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
  · exact (show Tendsto (fun x:ℝ=> (x:ℂ)) (𝓝 0) (𝓝 0) by simpa using Complex.continuous_ofReal.tendsto 0).comp he
  exact Eventually.of_forall fun n=> by unfold trek; simp
lemma trainWave (h:Package η a b c P v G U V)(x:Cover):dew (trackV x) (prog G) 0=Complex.I • hiss (trackV x):=by
  let L := trackV x
  let J:= (fun k=> model (Dir v k)); let R:= prog G
  have he: ∀ᶠ n:Side in atTop,R ((trek n) • L)= J ((trek n) • L):=by
    filter_upwards [lifts x] with n hn
    rw [show trek n • L=tuning (wrap n x) from ?_]; exact zoom h _
    ext1 i; simp only [tuning,menu,spacer,hn,Pi.smul_apply,smul_eq_mul, trek, Complex.ofReal_mul]; rfl
  let V (t:ℂ):= t • L
  have hp:HasDerivAt V L 0:=by simpa using! ((hasDerivAt_id' (0:ℂ)).smul_const L)
  have h0 : V 0=0:=zero_smul ..
  let T:= R ∘ V; let W:= J ∘ V
  have ht : HasDerivAt T (dew L R 0) 0:=by have hh:= ((show DifferentiableAt ℂ R (V 0) from h0 ▸ (prog_demand h L).1).hasFDerivAt.comp_hasDerivAt _ hp); rw [h0] at hh; exact hh
  have hz : DifferentiableAt ℂ J (V 0):=by rw [h0]; exact Para.signal.toContinuousLinearMap.differentiableAt.comp 0 (show DifferentiableAt ℂ _ _ from iris (Dir_budget P.good (fun _:Unit=>v)) ())
  have hw: HasDerivAt W (dew L J 0) 0:=by have hh:=hz.hasFDerivAt.comp_hasDerivAt _ hp; rw [h0] at hh; exact hh
  have hh : T ∘ trek =ᶠ[atTop] W ∘ trek:=he
  have ha:= advance_0; have hf:=ha.mono_right nhdsWithin_le_nhds; have hc:T 0=W 0:=tendsto_nhds_unique ((ht.continuousAt.tendsto.comp hf).congr' hh) (hw.continuousAt.tendsto.comp hf)
  rw [← gust_v v P.good]; change _=dew L J 0
  exact tendsto_nhds_unique (((hasDerivAt_iff_tendsto_slope_zero.mp ht).comp ha).congr' (he.mono fun n hn=> show _=_ from by dsimp only [Function.comp_apply]; rw [zero_add,hc, show T (trek n)=W (trek n) from hn])) ((hasDerivAt_iff_tendsto_slope_zero.mp hw).comp ha)
lemma halis (h:Package η a b c P v G U V)(i:Axis): dew (step i) (prog G) 0=Complex.I • wave (gamma i):=by
  have h1:= trainWave h (step i); have h2:= trainWave h (0:Cover)
  let q:=2*(Real.pi:ℂ); have hq:q≠0:=mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  let f (p:Momentum):= model (Dir v p)
  rw [← gust_v v P.good] at h1 h2
  have ht : q • (step i:Momentum)=trackV (step i)-trackV 0:=by
    ext1 a; by_cases he : i=a; · simp [trackV,q,fixed,he]; ring
    simp [trackV,q,fixed,Ne.symm he]
  have hv : dew (step i) (prog G) 0=dew (step i) f 0:=by apply smul_right_injective Bundle hq; simp only []; unfold dew;  rw [← map_smul,← map_smul,ht,map_sub,map_sub]; unfold dew at h1 h2; rw [h1,h2]
  rw [hv]; unfold f; rw [gust_v v P.good]; simp [hiss,ite_smul]
lemma at_sea (h:Package η a b c P v G U V)(i:Axis):v₁ G U C i 0=touch (echo C)*wave (gamma i):=by
  have he:= (prog_demand h (step i)).2
  unfold v₁; change _+(∑' j,nil₁ C (U j) i 0 0)=_; simp_rw [nil₁,hack0,zero_smul,zero_mul,tsum_zero,add_zero]
  change (∑' j,boom₁ C (G j) i 0 0)=_; simp_rw [boom_jet]; rw [(he.mul_left (touch (echo C))).const_smul (-Complex.I) |>.tsum_eq,halis h i,Matrix.mul_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]
end YM.QCD.Pearl
