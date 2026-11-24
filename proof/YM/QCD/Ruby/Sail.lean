import YM.QCD.Ruby.Rows
/-! # repetition taxes at fine monitor. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees ConnectedActivityE6 Jets.Touch Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}{a u v w A R m k σ B' v' ht q':ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {p :ι→ℝ} {q:β→ℝ}
lemma scopes (hv: w>0)(hz: 0≤R)(hp:0≤q) (he:Ac.Hit (home X) B (taxed (oriD X) q R) a 1) (ht:1≤v)(hh:Real.exp A*w*v≤R)(hW:1≤w):Ac.Hit (home X) B ((metal X A)*taxed (oriD X) q v) a w⁻¹:=by
    intro x; have hm:= budget_scale (inv_pos.mpr hv).le (he x); rw [mul_one] at hm
    refine budget_mono hm (fun i=> ?_) fun i=>?_
    · unfold metal taxed; simp only [Pi.mul_apply]; split; exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg (zero_le_one.trans ht) _) (hp _))) (Real.exp_pos _).le; exact le_rfl
    split
    next h=>
       dsimp only [Pi.mul_apply,metal,taxed]; rw [Real.exp_nat_mul,←mul_assoc,←mul_assoc,←mul_assoc] -- inspect
       apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; apply mul_le_mul_of_nonneg_right _ (hp _)
       let i':=(oriD X i).card; have ht':1 ≤ i':=(Finset.card_pos.mpr (X.addr i).alive)
       rw [mul_comm (w⁻¹), ← div_eq_mul_inv, le_div_iff₀ hv]; apply le_trans ?_ (pow_le_pow_left₀ (by have h:=zero_lt_one.trans_le ht; positivity) hh _); rw [mul_pow,mul_pow,mul_right_comm]; -- after
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_self_pow₀ hW (Nat.ne_of_gt ht')) (pow_nonneg (Real.exp_pos _).le _)) (pow_nonneg (zero_le_one.trans ht) _)
    next=> rw [mul_zero]
lemma portends (L:Side) (M a:ℝ) (hp:0<M)(he:0≤a) : ∀ᶠ x in atTop, let R:= radiusB x; let V:=taxK L x 1
    ∀ (c:Side)(N:ℕ) (ι β:Type) (Y:Hue c N ι)(X:Rail c N β) (p:ι→ℝ)(q:β→ℝ)(t b:ℝ), 0≤p→ 0≤q→(∀ i U, ‖token c N b (Y.mean i U)‖≤ p i)→(∀ i U, ‖token c N b (X.warp i U)‖≤ q i)→
      Ac.Hit (home X) R (taxed (oriD X) q (Real.exp (Delay.hatWin su L (M/2) (1/2) x))) (a+1) 1 → Ac.Hit Y.bud R p (a+1+1) (pra L x) →
      Ac.Hit (home (Trail Y X t)) R (taxed (oriD (Trail Y X t)) (fair Y X p q) V) a 1 :=by
  let g x:=taxK L x 1; have hY : Rate su L (-1) (fun x=>(g x)⁻¹):= couplings L zero_lt_one
  let f x:=(g x)⁻¹+(g x)⁻¹*Animals.ballCost (radiusB x)*pra L x
  have ht:=expensed (L:=L) 0 1 0 ; simp only [one_mul] at ht
  have hh: Rate su L (-1) f:=by
     apply hY.add; have hx:= (hY.mul ht.ruled).mul Rate.monitor; simpa only [add_zero] using hx
  have hk : Rate su L (-1) (fun x=> degreePrice (radiusB x) (f x) 1):=by
     unfold degreePrice stretch; simp only [div_one]; have he := (ht.ruled.mul hh).mul_left 4; simpa only [zero_add] using he
  filter_upwards [Seat.your L|>.eventually_ge_atTop 1, (hh.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 zero_lt_one, hk.below (by norm_num) (1/2) (by norm_num),Seat.your L|>.eventually_ge_atTop (12/M)] with x HX HH h hF
  have hZ : 1 ≤ taxK L x 1:= Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le)
  intro B V c N ι β Y X p q t b h1 h2 h3 h4 h5 h6 y
  let r:=f x; have hx:0<r:=by unfold r f; have h:=zero_lt_one.trans_le HX; have hG:0<g x:=zero_lt_one.trans_le hZ; positivity
  refine budget_loosen ((renowned Y X h1 h2 h3 h4 hZ hx zero_lt_one he (by norm_num) ((le_abs_self _).trans h) h6 (scopes X (zero_lt_one.trans_le hZ) (Real.exp_pos _).le h2 h5 hZ ?_ hZ) le_rfl).2 y) ((le_abs_self _).trans HH)
  rw [taxK,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  have hp' : fan L (1/3) x≤pra L x:= (Real.rpow_le_rpow_of_exponent_le HX (by norm_num : (1:ℝ)/3≤1)).trans_eq (Real.rpow_one _)
  have hx:= (div_le_iff₀ hp).1 hF; unfold Delay.hatWin; change pra L x+1*fan L (1/3) x+1*fan L (1/3) x≤ M/2*(1/2)*(pra L x)^2; linarith only [hp', mul_le_mul_of_nonneg_right hx (zero_le_one.trans HX)] -- syntax
end YM.QCD.Ruby
