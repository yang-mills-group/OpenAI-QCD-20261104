import YM.QCD.Kites.Expense
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Currency
/-! # buying gauges in the output. No claims on actual stage lower threshold M curve vs continuum scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{X:St c}{ι β ν α ι':Type}
open WilsonStartup Collection Averaging Pressure Jets.Touch Time ConnectedActivityE6
variable (S: RG.Stage)
structure Now (L:Side)(p:BudgetPoint)(S: RG.Stage)(x:ℝ):Prop where
 era : Same S p
 baseG: p.threshold=fiery su x L
 ball: p.B=radiusB (betaF su x L)
lemma plusT (p : RG.Stage) (h:p.clip.direct ≤1): ∀ᶠ x:ℝ in atTop, ∀ a:BudgetPoint, p.supportExponent=a.supportExponent → a.B=radiusB x→ a.threshold=temp x → Decent p.clip a ∧ Geo.Width a p.clip p.width:=by
    have hp:= Work.E01.radiusB_tendsto
    have he := ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hp).const_mul_atTop p.width_pos
    filter_upwards [Real.tendsto_log_atTop.eventually (Timing.cut p.clip),hp.eventually_ge_atTop 2, eventually_gt_atTop 1, he.eventually_ge_atTop (4*(p.supportExponent+1))] with x hx hv hk hM a hP ha hX
    have ht : a.B =Timing.balls (Real.log x):=ha
    have hh:= Time.threshold_aligned x (zero_lt_one.trans hk); have hI : a.threshold=Timing.temp (Real.log x):= hX.trans ((Eq.trans (show Pressure.temp x=_ from rfl) hh.1.symm).trans hh.2.symm)
    refine ⟨⟨h,ha ▸ hv,(by rw [ht,hI]; exact hx)⟩,⟨p.width_pos,p.slow_selector, (div_le_iff₀ (by exact_mod_cast a.B_pos)).mpr ?_⟩⟩
    rw [ha,← hP]; change 4*(p.supportExponent+1) ≤ p.width*(radiusB x:ℝ) at hM; linarith
-- numeric gates
lemma saleBudget (h:S.clip.direct≤1) (N:ℕ)(u t P:ℝ)(hu:1≤u)(ht:1≤t)(hp:1≤P):∃ K:ℝ,0<K ∧ ∀ L:Side,∀ D:ℝ,0 < D → ∀ B:ℕ, ∀ᶠ x in atTop,∀ p:BudgetPoint, Now L p S x→B ≤ p.B ∧ Decent S.clip p ∧ Geo.Width p S.clip S.width ∧∀ r:ℝ, |r| ≤ D →
       u*(K*chip L x) ≤ 1/2 ∧ bankH t u P (K*chip L x) N p S.clip S.width S.paths r ≤1 ∧ billH t u P (K*chip L x) N p S.clip S.width S.paths r ≤ chip L x ∧ drains t u P (K*chip L x) N p ≤ p.threshold^2 :=by
    let Z:=convertQ S t u P N; have he := chippos (t:=t) (w:=u) (P:=P) S N ht hu hp; change 0≤Z at he; let K:=1/(2*(1+Z)); have hh :0<K:=by unfold K; positivity
    refine ⟨K,hh,fun L D hD B=>?_⟩
    have hv: Z * K ≤ 1/2:=by
       unfold K; rw [mul_one_div]; apply (div_le_iff₀ (by positivity)).2; linarith
    let A:= Time.top su S; have ht':= (base_nonneg su S).2
    let X := drains t u P K N (Time.probe S); let β:=fun x=> betaF su x L; have hm:=Work.E09.betaF_growth su L
    filter_upwards [ (hm.eventually (plusT S h)), hm.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop B), banca (r:=t) (u:=u) (P:=P) S hp ht hu L K D hh hD N, event_chip L 0, (((Jets.Touch.chip_rate L).mul_left K).mul_left u).below (by norm_num) (1/2) (by norm_num), dawn L t (1/2) (A*D) (by norm_num), under L (max 1 X) 1 zero_lt_one (lt_of_lt_of_le zero_lt_one (le_max_left ..))] with x hV hJ hF hh' hC hZ h'
    intro p hS; obtain ⟨hy,hX,hk⟩:=hS; obtain ⟨hL,hQ⟩ := hV p hy.2.2.symm hk hX
    refine ⟨hk ▸ hJ,hL,hQ,fun r hx=>⟨(le_abs_self _).trans hC,hF p hy hk hX r hx,?_ ,?_⟩⟩
    · let t':=p.threshold; have hπ:=p.threshold_pos
      rw [polynomialH _ _ _ _ _ _ _ hy]; apply le_trans (add_le_add (b:=1/2*chip L x) (d:=A*(D*t'^3)) (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hv hh'.2.1.le) (by exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (pow_nonneg hπ.le _)) ht'))
      have hI : A*(D*t'^3)≤1/2*chip L x:=by unfold t'; rw [← mul_assoc,hX]; exact (le_abs_self _).trans hZ
      linarith
    let v:=chip L x; have hp': drains t u P (K*v) N p=X*v:=by unfold X drains scoreT; rw [feeCu _ hk hy]; unfold Quotes.preExponent Time.probe; rw [hy.2.2]; simp only; ring
    rw [hp',hX]; rw [one_mul] at h'; exact (mul_le_mul_of_nonneg_right (le_max_right ..) hh'.2.1.le).trans h'
lemma birthed (L:Side)(t κ:ℝ)(hk:0<t)(ht:0<κ):∀ᶠ x in atTop,0<haloK L x ∧ haloK L x≤t ∧ fiery su x L ≤κ*haloK L x ^2 :=by
    filter_upwards [kentucky L hk, filming L ht 1] with x hx hv
    refine ⟨hx.1,hx.2.1,?_⟩; unfold coneK at hv; have hg:= mul_self_nonneg (haloK L x)
    -- hv pos threshold from hx?
    by_cases hi:0 ≤ fiery su x L; · have he: (1:ℝ)≤ ((radiusB x:ℝ)+1)^5:= one_le_pow₀ (by simp); nlinarith [mul_le_mul_of_nonneg_right he hi,mul_nonneg ht.le hg]
    exact (le_of_not_ge hi).trans (mul_nonneg ht.le (sq_nonneg _)) -- lt issue
lemma framesC (L:Side) (u:ℝ) (h:0<u):∀ᶠ x in atTop, 2≤ pra L (betaF su x L) ∧ 1≤ fan L u x ∧ taxK L x 1≤taxK L (betaF su x L) 1 ∧ fan L u x≤ fan L u (betaF su x L) :=by
    let g:=fun x => betaF su x L; have he:=Work.E09.betaF_growth su L; have hh:∀ x:ℝ,x≤g x:= fun x=>le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le (Real.log_nonneg (by exact_mod_cast L.pos)))
    filter_upwards [he.eventually ((Touch.Seat.your L).eventually_ge_atTop 2),(Touch.Seat.your L).eventually_ge_atTop 1,(Real.tendsto_log_atTop.comp he).eventually_ge_atTop 1,he.eventually_gt_atTop 0] with x hx ht hf hX
    let p:= pra L x; have hp:= Delay.monitor_pos su L x; have hv : pra L x ≤ pra L (betaF su x L):=by
       have ht:=hh (g x); apply Real.exp_monotone; change (Real.log (Real.log (g x)))^2 ≤ (Real.log (Real.log (g (g x))))^2; gcongr
       exact Real.log_nonneg hf
    refine ⟨hx,Real.one_le_rpow ht h.le,?_ , Real.rpow_le_rpow hp.le hv h.le⟩; apply Real.exp_monotone; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le hv (by norm_num)) zero_le_one
end YM.QCD.Kites
