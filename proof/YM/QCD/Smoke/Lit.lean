import YM.QCD.Smoke.Oath

/-! # log germ at an actual torus matrix. Use matrix log (scalar only after extracting local diagonal blocks). -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Finset Lat Cost Run Eyrie Metric Lattice Wilson Stationary
open YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.L2Operator
variable {n:Side} {X Y Z:Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z]
lemma blade_over {F:X→Y}{G:Y→Z}{x:X}(v:X)(h:ContDiffAt ℝ ω F x)(hg:ContDiffAt ℝ ω G (F x)): blade v (G ∘ F) x=blade (blade v F x) G (F x):= by unfold blade; rw [fderiv_comp _ (hg.differentiableAt (by simp)) (h.differentiableAt (by simp))]; rfl
lemma area_eval {F:X→Y}{G:Y→Z}{x:X}(v w:X)(h:ContDiffAt ℝ ω F x)(hg:ContDiffAt ℝ ω G (F x)): Jacobi.mixed v w (G∘F) x=Jacobi.mixed (blade v F x) (blade w F x) G (F x)+blade (Jacobi.mixed v w F x) G (F x):=by
  have he := ((h.eventually (by simp)).and (h.continuousAt.tendsto.eventually (hg.eventually (by simp)))).mono fun i hi=>blade_over (F:=F) w hi.1 hi.2
  let g:= fderiv ℝ G; let B:=blade w F
  let M:= g ∘ F; let Q:= fun i=> M i (B i)
  have hQ: blade w (G ∘ F)=ᶠ[𝓝 x] Q:=he
  have hp:= hg.fderiv_right (m:=ω) (by simp); -- inspect
  have hM: ContDiffAt ℝ ω M x:= hp.comp x h; have hB : ContDiffAt ℝ ω B x:= smooth w h
  let V:= ContinuousLinearMap.apply ℝ Z (B x) -- inspect
  have hu : blade v Q x=blade v M x (B x) + M x (blade v B x):=by
    unfold Q blade; rw [fderiv_clm_apply (hM.differentiableAt (by simp)) (hB.differentiableAt (by simp))]; exact add_comm ..
  have hh : blade (B x) G = V∘g:=rfl
  change blade v _ x=blade (blade v F x) (blade (B x) G) (F x)+_
  rw [blade_same v hQ, hu,hh,retell _ _ hp, show blade v M x=_ from blade_over (G:=g) v h hp]; rfl
variable {M:Sheet n}
lemma chip_omega (i:ℕ):ContDiff ℂ ω (fun x:Sheet n=> logchip x i):=by unfold logchip; fun_prop
lemma lit (he: ‖M‖ < 1) : ContDiffAt ℝ ω lap M ∧ ∀ j:ℕ,∀ p:Fin j→Sheet n,HasSum (fun i=> iteratedFDeriv ℝ j (fun X=>logchip X i) M p) (iteratedFDeriv ℝ j lap M p):=by
  obtain ⟨r,hr,hZ⟩:= exists_between he; let d:=r-‖M‖
  have hd:0 < d:=sub_pos.mpr hr
  let f i (X:Sheet n):= logchip X i
  let a (i:ℕ):=r^(i+1)
  have ha : Summable a:= by
    exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one ((norm_nonneg _).trans hr.le) hZ) -- name
  have hp i X (hx:X∈ball M d): ‖f i X‖ ≤ a i:= by
    apply (mark_norm X i).trans; unfold a; gcongr; have hv := (mem_ball.mp hx); rw [dist_eq_norm] at hv; have hk:=norm_sub_norm_le X M; unfold d at hv; linarith
  have hm : ContDiffAt ℂ ω (lap: Sheet n→Sheet n) M:= (Work.F02.analytic_series f hd (fun i=> (chip_omega i).differentiable (by simp)) ha hp).contDiffAt
  refine ⟨hm.restrict_scalars ℝ,fun i p=>?_⟩
  have H:= circles M hd _ ha (fun i=> chip_omega (n:=n) i) hp i M (mem_ball_self (by positivity)); have hR := (hm.of_le (show (i:WithTop ℕ∞)≤ω from le_top)).restrictScalars_iteratedFDeriv (𝕜:=ℝ)
  have hQ j:= ((chip_omega (n:=n) j).contDiffAt.of_le (show (i:WithTop ℕ∞)≤ω from le_top)).restrictScalars_iteratedFDeriv (𝕜:=ℝ) (x:=M) -- name
  simp_rw [← hR,← hQ]; exact (ContinuousMultilinearMap.apply ℂ _ _ p).hasSum H

lemma lapRates (F:X→Sheet n) (h:ContDiffAt ℝ ω F 0)(hp : ‖F 0‖<1): ContDiffAt ℝ ω (lap ∘ F) 0 ∧ ∀ x y, HasSum (fun i=> blade x ((fun X=>logchip X i)∘F) 0) (blade x (lap ∘ F) 0) ∧ HasSum (fun i=> Jacobi.mixed x y ((fun X=>logchip X i) ∘ F) 0) (Jacobi.mixed x y (lap ∘ F) 0):=by
  have he:= lit hp
  have hh i : ContDiffAt ℝ ω (fun X=> logchip X i) (F 0):= (chip_omega i).contDiffAt.restrict_scalars ℝ
  have h (x):HasSum (fun i=> blade x (fun X=>logchip X i) (F 0)) (blade x lap (F 0)):=by
    have h:=he.2 1 ![x]; simp_rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero] at h; exact h
  rename_i T
  refine ⟨he.1.comp 0 T, fun x y=>?_⟩
  simp_rw [blade_over x T (hh _),blade_over x T he.1,area_eval x y T (hh _), area_eval x y T he.1,iter (x:=F 0) _ _ (hh _),iter _ _ he.1] -- see
  exact ⟨h _, (he.2 _ _).add (h _)⟩
end YM.QCD.Smoke
