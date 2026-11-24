import YM.QCD.Finch.Offer
import YM.QCD.Finch.Wait
/-! # x clocks. L committed. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f L :Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
open Garden Para Metric Set
variable {t s τ u r d ε α η K :ℝ}{j k:ℕ}{B:BudgetPoint}
open Jets.Touch Push Push.AbsoluteSums Footprint
noncomputable def Emax (L:Side)(p v h:ℝ):ℝ:= v * Jets.Touch.chip L p / h^2
abbrev speedP (L:Side)(θ s:ℝ):ℝ:= 2*fan L θ s
noncomputable def roofK (L:Side)(θ ν x:ℝ):ℝ:= Emax L x ν (speedP L θ x)/L.val
abbrev lng (t:ℝ):= Real.log (Real.log t)^2
lemma rH (d:ℝ)(hd:0≤d) : Tendsto (fun x=>lng (x+d)-lng x) atTop (𝓝 0):=by
   apply Metric.tendsto_nhds.mpr; intro ε he
   let p:= ε/(1+d); have hp:0<p:= by unfold p; positivity
   let g x:= 2*(Real.log (Real.log x)) * (x*Real.log x)⁻¹
   have hh :∀ᶠ x:ℝ in atTop,HasDerivAt lng (g x) x ∧ ‖g x‖ ≤ p:=by
      filter_upwards [eventually_gt_atTop 1,Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (2/p)] with x hx hk ht
      have h:0<x:=(by linarith); have hK : 0<Real.log x:=Real.log_pos hx
      have hh:= ((Real.hasDerivAt_log hK.ne').comp x (Real.hasDerivAt_log h.ne')).pow 2
      refine ⟨?_,?_⟩
      · convert hh using 1<;> first|rfl| (unfold g; norm_num)
      have ht: (2:ℝ)≤ x*p:= (div_le_iff₀ hp).1 ht
      have hv:0 ≤ Real.log (Real.log x):= Real.log_nonneg hk
      rw [Real.norm_of_nonneg (show 0 ≤ g x from (by unfold g; positivity))] -- argument
      unfold g; rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; have hz:= Real.log_le_sub_one_of_pos hK; linarith only [hz, mul_le_mul_of_nonneg_right ht hK.le]
   obtain ⟨a,ha⟩:= eventually_atTop.1 hh; filter_upwards [eventually_ge_atTop a] with x hx; let X:= Icc x (x+d); have hh(y)(hy:y∈ X):= ha y (hx.trans hy.1); rw [dist_zero_right]; apply lt_of_le_of_lt ((convex_Icc x (x+d)).norm_image_sub_le_of_norm_hasDerivWithin_le (fun i hi=> (hh i hi).1.hasDerivWithinAt) (fun i hi=> (hh i hi).2) (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)))
   rw [add_sub_cancel_left,Real.norm_of_nonneg hd]; unfold p; rw [ div_mul_eq_mul_div,div_lt_iff₀ (by positivity)]; linarith
variable (L:Side)
local notation "d₀"=> su.slopeConstant*Real.log L.val
local notation "φ"=> fun x:ℝ=>Pressure.betaF su x L
lemma rol (h:ℝ):Tendsto (fun x=>fan L h (φ x)/fan L h x) atTop (𝓝 1):=by
   have he:0 ≤ d₀:=mul_nonneg (Gauge.slopeConstant_pos simple).le (Real.log_nonneg (by exact_mod_cast L.pos))
   have hz:= Real.continuous_exp.continuousAt.tendsto.comp (((rH _ he).comp (Work.E09.betaF_growth su L)).mul_const h); rw [zero_mul,Real.exp_zero] at hz; refine hz.congr fun x=>?_ ; unfold fan; dsimp only [Function.comp_apply]; change _= Real.exp _ ^ h / Real.exp _ ^ h; rw [← Real.exp_mul,←Real.exp_mul,← Real.exp_sub]; congr 1; rw [sub_mul]; rfl
lemma dim (h:ℝ) :∀ᶠ x in atTop, fan L h (φ x) ≤ 2*fan L h x:=by filter_upwards [(rol L h).eventually_le_const (by norm_num : (1:ℝ)<2)] with x hx; exact (div_le_iff₀ (fan_pos ..)).1 hx
local notation "P"=> Jets.Touch.chip
lemma pegL :∀ᶠ x in atTop,P L x ≤ 2*P L (φ x) ∧ P L (φ x) ≤ 2*P L x:=by
    have he:∀ᶠ x in atTop, pra L x ≤ pra L (φ x):= by
         filter_upwards [framesC L 1 zero_lt_one] with i hi; simpa only [fan, Real.rpow_one] using hi.2.2.2
    have hD:0 ≤ d₀:=mul_nonneg (Gauge.slopeConstant_pos simple).le (Real.log_nonneg (by exact_mod_cast L.pos))
    filter_upwards [he,dim L 1,Delay.shift_pos su L,(Work.E09.betaF_growth su L).eventually_ge_atTop d₀] with i hi hv hx hp
    let x:= betaF su i L; have hh:0<x:=hx; have hp':0<x+d₀:=(by linarith); have hz:= Delay.monitor_pos su L i
    change x⁻¹*pra L i≤2*((x+d₀)⁻¹*pra L x)∧(x+d₀)⁻¹*pra L x≤ 2*(x⁻¹ * pra L i); constructor
    · rw [← mul_assoc]; apply mul_le_mul _ hi hz.le (by positivity); rw [← div_eq_mul_inv,le_div_iff₀ hp']; change d₀≤ x at hp; field_simp; linarith
    simp only [fan,Real.rpow_one] at hv; rw [mul_left_comm 2]; exact mul_le_mul (inv_anti₀ hh (by linarith)) hv (Delay.monitor_pos ..|>.le) (by positivity) -- hp fix
lemma pivotal (S:Stage)(K:ℝ)(he:0<K):∀ᶠ x in atTop, let p:=radiusB x; let t:= S.supportExponent+1
    payment 1 (4*p+2) 0 1 1 (flowM L x) t 0+ payment 1 (4*p+2) 0 1 1 (K* P L x) t 0≤1:=by
     let z:= handQ S 6 0 0 1 1; let p x:=(1+(radiusB x:ℝ))^4; have ht:Rate su L 0 p:=by have h:= (Seat.comb (Seat.numbers 1) (Touch.Seat.radius (L:=L))).powered 4; exact h.ruled
     let a:ℝ := -(3/10); have hh:Rate su L a (fun x=> p x*z*(flowM L x)+(p x*z*(K*P L x))):=by
         apply Rate.add; · simpa using (ht.mul_right z).mul (show Rate su L a (flowM L) from Rate.power)
         apply ((ht.mul_right z).mul ((chip_rate L).mul_left K )).weaken; unfold a; norm_num
     filter_upwards [event_chip L 0,hh.below (by unfold a; norm_num) 1 zero_lt_one] with x hx hz; intro P₀ t; exact (add_le_add (hunger S 0 0 1 zero_le_one (flowM L x) (Real.rpow_nonneg hx.1.le _) (radiusB x)) (hunger S 0 0 1 zero_le_one (K*P L x) (mul_nonneg he.le hx.2.1.le) (radiusB x))).trans ((le_abs_self _).trans hz)
-- payment α' K* chip prev→ rewrite coarser.
end YM.QCD.Finch
