import YM.QCD.Lunar.Milky
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
namespace Ring0
variable {A : Pot G c}{G':Gauge}
noncomputable abbrev pass (v:Dir G c)(u:ℝ): Config G c:= increment 1 (u • v)
lemma past (U : Config G c)(A:Dir G c)(s t:ℝ): increment (increment U (t • A)) (s • A)= increment U ((s+t) • A) :=by
  funext i; apply G.mat_injective
  simp only [increment, G.mat_mul, Pi.smul_apply, G.mat_lieExp, map_smul, add_smul, map_add, ← mul_assoc]
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  apply congr_arg (fun x => x * G.mat (U i))
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (A i))).smul_left s).smul_right t)).symm
lemma roar (hp:P.Regular W A)(ht:P.supBounds o W A a) (v:Dir G c)(h:G.Simple)(hk:P.dirBound o v)(hu:0<t) (hV:∀ i:ℝ,i ∈ Set.Icc 0 t → Healthy P.threshold W (pass v i)) :
   |logHessian A v v|≤a ∧ ∀ i:ℝ,i ∈ Set.Icc 0 t→ |A (pass v i)-A 1 - i^2*(logHessian A v v)/2| ≤ i^3*a :=by
   let f(i:ℝ):= A (pass v i); let K:= Set.Icc 0 t; have h0 : 0∈K:= ⟨le_rfl,hu.le⟩
   have hj:= P.order_ge; have hl: ↑(3:ℕ) ≤(P.order : WithTop ℕ∞) := Nat.cast_le.mpr (by omega)
   have hv(i)(he:i∈K) :ContDiffAt ℝ ↑(3:ℕ) f i:=by
        let d (u:ℝ):= (u-i) • v; have he0:d i=0:=by simp [d]
        have hp : ContDiffAt ℝ ↑P.order ((fun X=>A (increment (pass v i) (d X)))) i:=(show ContDiffAt ℝ (↑P.order) (A ∘ increment _) (d i) from he0.symm ▸ (hp.smooth _ (hV i he))).comp i (by unfold d; fun_prop)
        rw [show f=fun X=>A (increment (pass v i) (d X)) from funext fun x=>by unfold f d pass; rw [past,sub_add_cancel]]; exact hp.of_le hl
   have hm (j:ℕ)(p:ℝ)(hh : j≤3)(h':p∈K) : ‖iteratedDeriv j f p‖ ≤ a:=by
      unfold f pass; rw [← Next.Foundations.leftDerivs_diag]; exact ht.2 (pass v p) (hV p h') _ (by simp; omega) (fun x hx=> (List.eq_of_mem_replicate hx).symm ▸ hk) -- lemma
   have hX : iteratedDeriv 2 f 0=logHessian A v v:=by
        unfold f pass; rw [← Next.Foundations.leftDerivs_diag,hessian_diag h hp,zero_smul,AnalyticBridge.VerifiedReset.at_zero]; rfl
   have hM : iteratedDeriv 1 f 0=0:=by
      have he: fderiv ℝ (germ A) 0 v=0:=by rw [flat_critical h hp]; rfl
      rw [iteratedDeriv_one]; exact (Push.side (germ A) ((germ_diff hp).differentiableAt (by norm_num)) v).deriv.trans he
   refine ⟨hX ▸ hm 2 0 (by omega) h0,fun i hi=>?_⟩
   have hg (z j)(hp : z∈K)(hc : j ≤3) : iteratedDerivWithin j f K z=iteratedDeriv j f z:= iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu) ((hv z hp).of_le (by exact_mod_cast hc)) hp
   have hq := taylor_mean_remainder_bound (n:=2) (f:=f) hu.le (fun i hi=> (hv i hi).contDiffWithinAt) hi (C:=a) (fun q h=> by rw [hg _ _ h le_rfl]; exact hm _ _ le_rfl h)
   have hh0 : f 0=A 1:=by unfold f pass; rw [zero_smul, AnalyticBridge.VerifiedReset.at_zero]
   have hq' : taylorWithinEval f 2 K 0 i = A 1+i^2*(logHessian A v v)/2:=by
      rw [taylor_within_apply]; simp only [Nat.reduceAdd, sum_range_succ, sub_zero]; rw [hg _ _ h0 (by decide), hg _ _ h0 (by decide), hg _ _ h0 (by decide)]; norm_num [Nat.factorial,hX,hM,hh0]; ring
   change ‖f i-_‖ ≤ _ at hq; rw [show taylorWithinEval ..= _ from hq',Real.norm_eq_abs] at hq
   rw [sub_sub]; refine hq.trans ?_ ; have ht':0 ≤ i :=hi.1; have h':=ht.1; norm_num [Nat.factorial]; nlinarith only [mul_nonneg h' (pow_nonneg ht' 3)]
lemma lin (v: Dir G c) (P:BudgetPoint): ∃ t:ℝ,0<t ∧∀ u:ℝ,u∈Set.Icc 0 t→ flags P.threshold (pass v u)=∅:=by
   -- eventual via flags
   have hp:Continuous (pass v):=by
       have h : Continuous (increment (1:Config G c)):=by unfold increment; fun_prop
       exact h.comp (continuous_id.smul continuous_const)
   have h0:pass v 0=1:=by rw [pass,zero_smul, AnalyticBridge.VerifiedReset.at_zero]
   have hx : ∀ᶠ u in 𝓝 (0:ℝ), flags P.threshold (pass v u)=∅:= by
           refine (eventually_all.mpr (show ∀ p:Face (Per c), ∀ᶠ u in 𝓝 (0:ℝ), G.chord (faceValue (pass v u) p) ≤ P.threshold from ?_)).mono (fun i h=> Push.BetaTransport.flags_empty h)
           intro p; let y(u:ℝ):=G.chord (faceValue (pass v u) p); have h1(y' : Face (Per c)):faceValue (1:Config G c) y'=1:=by simp [faceValue,travel,square]
           have hc :Continuous y:=by unfold y faceValue; fun_prop
           exact (hc.tendsto 0).eventually (ge_mem_nhds (by unfold y; rw [h0,h1,chord_one]; exact P.threshold_pos))
   obtain ⟨p,hp,hP⟩:= Metric.mem_nhds_iff.mp hx; refine ⟨p/2,half_pos hp,fun i hi=>hP (Metric.mem_ball.mpr ?_)⟩; rw [dist_zero_right, Real.norm_of_nonneg hi.1]; exact hi.2.trans_lt (half_lt_self hp)
end Ring0
end YM.QCD.Lunar
