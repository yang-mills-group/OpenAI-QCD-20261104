import YM.QCD.Fall.Bake
import YM.QCD.High.Yang
import YM.QCD.Finch.Tissues
/-! # Publishing markers at strong enough thresholds for analytic K radius continuation. Only price not symmetry/Tall carried in this version. -/
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

open Kites
abbrev SoftCost (Y:Hue c N ι)(B:ℕ)(a u t:ℝ): Prop:= ∃ y:ι→ℝ, Ac.Hit Y.bud B y a u ∧∀ i V, ‖token c N t (Y.mean i V)‖≤ y i
lemma cashSoft (hp:Stew.Purchases Y t B a A v): SoftCost Y B a A v:=by obtain ⟨p,h,hx⟩:=hp.paint; exact ⟨p,hx,h⟩
lemma scantSoft (hp:SoftCost Y B a A v)(hC:u ≤ a)(hB:A ≤ R): SoftCost Y B u R v:=by
    obtain ⟨y,hY,hy⟩:=hp; exact ⟨y,fun i=>budget_loosen ((Shells.Warmlet.fresh y _ hY hC (fun i=> (norm_nonneg _).trans (hy i 1))) i) hB,hy⟩
def StackK (B:ℕ)(R m u a t h:ℝ):Prop:=∀ (c:Side)(N:ℕ)(ι β:Type)(Y:Hue c N ι)(X: Rail c N β)(s w:ℝ), SoftCost Y B t h w → Quits X B 1 R u w→ Quits (Trail Y X s) B 1 m a w
lemma stackForever (L:Side) (M a:ℝ) (hp:0<M)(he:0≤a) : ∀ᶠ x in atTop, let R:= radiusB x; let V:=taxK L x 8
    ∀ (c:Side)(N:ℕ) (ι β:Type) (Y:Hue c N ι)(X:Rail c N β) (p:ι→ℝ)(q:β→ℝ)(t b:ℝ), 0≤p→ 0≤q→(∀ i U, ‖token c N b (Y.mean i U)‖≤ p i)→(∀ i U, ‖token c N b (X.warp i U)‖≤ q i)→
      Ac.Hit (home X) R (taxed (oriD X) q (Real.exp (Delay.hatWin su L (M/2) (1/2) x))) (a+1) 1 → Ac.Hit Y.bud R p (a+1+1) (pra L x) →
      Ac.Hit (home (Trail Y X t)) R (taxed (oriD (Trail Y X t)) (fair Y X p q) V) a 1 :=by
  let g x:=taxK L x 8; have hY : Rate su L (-1) (fun x=>(g x)⁻¹):= couplings L (by norm_num : (0:ℝ)<8)
  let f x:=(g x)⁻¹+(g x)⁻¹*Animals.ballCost (radiusB x)*pra L x
  have ht:=expensed (L:=L) 0 1 0 ; simp only [one_mul] at ht
  have hh: Rate su L (-1) f:=by
     apply hY.add; have hx:= (hY.mul ht.ruled).mul Rate.monitor; simpa only [add_zero] using hx
  have hk : Rate su L (-1) (fun x=> degreePrice (radiusB x) (f x) 1):=by
     unfold degreePrice stretch; simp only [div_one]; have he := (ht.ruled.mul hh).mul_left 4; simpa only [zero_add] using he
  filter_upwards [Seat.your L|>.eventually_ge_atTop 1, (hh.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 zero_lt_one, hk.below (by norm_num) (1/2) (by norm_num),Seat.your L|>.eventually_ge_atTop (68/M)] with x HX HH h hF
  have hZ : 1 ≤ taxK L x 8:= Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)
  intro B V c N ι β Y X p q t b h1 h2 h3 h4 h5 h6 y
  let r:=f x; have hx:0<r:=by unfold r f; have h:=zero_lt_one.trans_le HX; have hG:0<g x:=zero_lt_one.trans_le hZ; positivity
  refine budget_loosen ((renowned Y X h1 h2 h3 h4 hZ hx zero_lt_one he (by norm_num) ((le_abs_self _).trans h) h6 (scopes X (zero_lt_one.trans_le hZ) (Real.exp_pos _).le h2 h5 hZ ?_ hZ) le_rfl).2 y) ((le_abs_self _).trans HH)
  rw [taxK,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  have hp' : fan L (1/3) x≤pra L x:= (Real.rpow_le_rpow_of_exponent_le HX (by norm_num : (1:ℝ)/3≤1)).trans_eq (Real.rpow_one _)
  have hx:= (div_le_iff₀ hp).1 hF; unfold Delay.hatWin; change pra L x+8*fan L (1/3) x+8*fan L (1/3) x≤ M/2*(1/2)*(pra L x)^2; linarith only [hp', mul_le_mul_of_nonneg_right hx (zero_le_one.trans HX)] -- syntax

lemma skyHigh (L:Side)(M a:ℝ)(hp:0 < M)(he:0≤a): ∀ᶠ x in atTop, StackK (radiusB x) (priceK L M x) (taxK L x 8) (a+1) a (a+1+1) (pra L x) :=by
   filter_upwards [stackForever L M a hp he] with x hx; intro c N ι β Y X s w hA hX; obtain ⟨p,hp,h⟩:=hA; obtain ⟨q,hq,hQ⟩:= hX.cost; have hh:0 ≤ p := fun i=>(norm_nonneg _).trans (h i 1); have hf:0≤q:=fun i=>(norm_nonneg _).trans (hQ i 1)
   exact ⟨fair Y X p q,hx c N ι β Y X p q s w hh hf h hQ hq hp, fun i U=>haloP Y X hh hf h hQ i U⟩
lemma sunHigh (L:Side)(u a v:ℝ)(hz1:0<a)(he:0 ≤ u)(hq:0 ≤ v) :∀ᶠ x in atTop,StackK (highR L x) (taxK L x (v+3)) (taxK L x (v+1)) (u+a) u (u+a+1) 1:=by
    let f x:=taxK L x 1; let ux x:=(f x)⁻¹; let g x:ℝ:=16*(1+(highR L x:ℝ))^4; let m x:= ux x+ux x*g x; have hU:Rate su L (-1) ux:=couplings _ zero_lt_one; have hV:Rate su L 0 g:=(radH L).mul_left 16; have hM: Rate su L (-1) m:=by apply hU.add; simpa only [add_zero] using hU.mul hV
    have hJ:= (((hV.mul hM).mul_right a⁻¹).mul_left 4).below (by norm_num) (1/2) (by norm_num)
    filter_upwards [framesC L (1/3) (by norm_num),hJ, (hM.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 zero_lt_one] with x hx ht hn c N I V Y X s w hB hR
    obtain ⟨f',hf,hE⟩:=hR.cost; obtain ⟨b,hQ,hb⟩:=hB; have hZ :1 ≤ f x:= Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le); have hu:= zero_lt_one.trans_le hZ
    have hV1:1 ≤ taxK L x (v+1):= Real.one_le_exp (mul_nonneg (by linarith) (fan_pos ..).le)
    have hm : (Animals.ballCost (highR L x):ℝ) ≤ g x:=by unfold g Animals.ballCost; push_cast; have h0 := pow_le_pow_left₀ (show 0 ≤ (↑(highR L x):ℝ)+↑(highR L x)+1 by positivity) (show (↑(highR L x):ℝ)+↑(highR L x)+1≤2*(1+↑(highR L x)) by linarith) 4; linarith only [h0]
    have hg :0 ≤ g x:=by unfold g; positivity
    have hm':0 < m x:=by unfold m; have h: 0<ux x:= inv_pos.mpr hu; positivity
    have hv : 0≤ f':=fun i=>(norm_nonneg _).trans (hE i 1)
    obtain ⟨h₀,h₁⟩:=Ruby.renowned Y X (t:=s) (fun i=>(norm_nonneg _).trans (hb i 1)) hv hb hE hV1 hm' hz1 he (by norm_num : (1/2:ℝ)<1) (show degreePrice (highR L x) (m x) a ≤1/2 from (by unfold degreePrice Push.AbsoluteSums.Trees.stretch; refine le_trans ?_ ((le_abs_self _).trans ht); rw [div_eq_mul_inv]; gcongr)) hQ (Ruby.scopes X hu (Real.exp_pos _).le hv hf hV1 (by unfold f taxK; rw [← Real.exp_add, ←Real.exp_add]; apply Real.exp_monotone; linarith only [hx.2.1]) hZ) (by rw [mul_one]; exact add_le_add_right (mul_le_mul_of_nonneg_left hm (inv_pos.mpr hu).le) _)
    exact ⟨_,fun i=>budget_loosen (h₁ i) ((le_abs_self _).trans hn),h₀⟩

end YM.QCD.Ruby
#print axioms YM.QCD.Ruby.skyHigh
#print axioms YM.QCD.Ruby.sunHigh
