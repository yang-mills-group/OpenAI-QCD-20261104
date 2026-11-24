import YM.QCD.High.Tarp
/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
-- Scale/add proof. Weaken conditional for E heads. exact HASpanic.
variable {ι' μ:Type}
open Jets.Touch Lunar Pressure ConnectedActivityE6
local notation "rK" => (1/8 : ℝ)
local notation "ZK" => Real.exp rK
abbrev Steep (c:Side)(N:ℕ)(u:ℝ):Prop:= (max 1 u)^ (Fintype.card (Keys c N))≤ ZK
lemma lie (x :EvenA c N)(h:Steep c N t)(hp:0<t)(he:0<a) : Sen o a (wearK c N t x)≤ ZK*Sen o a x:=by
   rw [moments _ _ _ _ he.le hp.le]; unfold Sen; rw [Stew.plank,Stew.plank,pricesD _ (mul_pos hp he).le, pricesD _ he.le,Finset.mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [starch,mul_pow,← mul_assoc _ _ ‖_‖]; unfold starch; have hx : t^i.card≤ZK:= (pow_le_pow_left₀ hp.le (le_max_right ..) _).trans ((pow_le_pow_right₀ (le_max_left ..) (card_le_univ _)).trans h); apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (pow_pos he i.card).le) (Nat.cast_nonneg (α:=ℝ) (pieD (lens o) i))]
lemma lieK (x:EvenA c N)(h:Steep c N t) (hp:0<t)(he:0<a): ‖token c N a (wearK c N t x)‖≤ ZK *‖token c N a x‖:=by
    rw [skill,skill]; have hh y: ‖wearK c N y x‖= Creek.load (fun _=>y) x.val:=rfl; rw [show wearK c N a (wearK c N t x)=wearK c N (t*a) x from (by rw [mul_comm t]; exact Subtype.ext (Kites.makes x.val a t)),hh,hh]
    rw [Creek.dry _ (fun _=>mul_pos hp he),Creek.dry _ (fun _=>he),Finset.mul_sum]; apply sum_le_sum; intro i _; rw [prod_const,prod_const,mul_pow,← mul_assoc ZK]; apply mul_le_mul_of_nonneg_right _ (by positivity); exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ hp.le (le_max_right ..) _).trans ((pow_le_pow_right₀ (le_max_left ..) (card_le_univ _)).trans h)) (pow_pos he _).le
lemma more (X: Support c)(o:Site c)(h:o∈X)(B:ℕ) : (1:ℝ) ≤ coverNumber B X:=by
    obtain ⟨p,hp,hg⟩:=coverNumber_realized B X; obtain ⟨i,hi,-⟩:= halo_spec.mp (hp.1 h); rw [← hg]; exact_mod_cast card_pos.mpr ⟨i,hi⟩
variable (X:Gem c N ι) (Y: Patron.Rail c N β)
lemma greys (hv:Steep c N w)(hp:Licence p 2 t a X)(he:0<w)(ht:0<a): Licence p rK (Real.exp (-1)*t) a (flightE X w):=by
   obtain ⟨f,hf,H⟩:= hp.zone; let F:=flightE X w; refine ⟨fun i=>ZK*f i,fun i=> ?_,fun i=>?_⟩
   · refine budget_mono (budget_scale (Real.exp_pos _).le (hf i)) ?_ ?_
     · exact fun i=> ite_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (H i).travel) (Real.exp_pos _).le) le_rfl
     intro j; change ite ((X.addr j).site=i) _ _ ≤_; split
     next h=> dsimp only [flightE]; let q:ℝ:= coverNumber p.B (X.addr j).support; rw [mul_right_comm,←Real.exp_add, mul_comm (f j) _,←mul_assoc, ← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (H j).travel; apply Real.exp_monotone; linarith only [more _ _ (X.addr j).anchor p.B]
     next h=> rw [mul_zero]
   have ht':= (gust_local _ (H i)); exact ht'
where
   gust_local {u:ℝ}(i:ι)(hp:Woven (X.addr i).site (X.addr i).support p a (X.view i) u): Woven (X.addr i).site (X.addr i).support p a ((flightE X w).view i) (ZK*u):=by
       obtain ⟨hr,hg,hQ,hz,hV,hP⟩:= hp; let M:=songT (c:=c) (N:=N) w; change Woven _ _ _ _ (M ∘ X.view i) _; refine ⟨fun _ _ h=>congr_arg M (hr _ _ h),fun i=>dings _ _ _ (hg i),fun i h=>(M.contDiff.contDiffAt.comp 0 (hQ _ h)),?_,M.continuous.measurable.comp hV,mul_nonneg (Real.exp_pos _).le hP⟩
       intro i h' b z hχ; rw [Push.Local.left_linear M b (hQ i h') z]; exact (lie _ hv he ht).trans (mul_le_mul_of_nonneg_left (hz _ h' b z hχ) (Real.exp_pos _).le)
lemma verses (hp : Steep c N w)(h:Quits Y p.B 1 P 1 a)(he:0<w)(ha:0<a)(hz:0 ≤P):Quits (flightK Y w) p.B 1 P (rK+rK) a:=by
   obtain ⟨f,hf,H⟩:=h.cost; refine ⟨fun i=>ZK*f i,fun i=> ?_,fun i V=>(lieK _ hp he ha).trans (mul_le_mul_of_nonneg_left (H i V) (Real.exp_pos _).le)⟩; let g:= taxed (Ruby.oriD Y) f P; let X:=flightK Y w
   have hx(i):0 ≤ f i:=(norm_nonneg _).trans (H i 1); refine budget_mono (hf i) ?_ ?_
   · intro j; split; exact mul_nonneg (mul_nonneg (pow_nonneg hz _) (mul_nonneg (Real.exp_pos _).le (hx _))) (Real.exp_pos _).le; exact le_rfl
   intro j; change ite (i∈ Ruby.home Y j) _ _≤_; split
   next h'=>
       let v:ℝ:=coverNumber p.B (Ruby.home Y j); change (P^ (Ruby.oriD Y j).card*(ZK*f j))*Real.exp ((rK+rK)*v)≤ _; rw [mul_comm ZK, ← mul_assoc (P^_) (f j), mul_assoc (P^_*f j),←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hz _) (hx _)); apply Real.exp_monotone; unfold v; linarith only [more _ _ h' p.B]
   next _=> exact le_rfl
open Trees
lemma sunnyL (L:Side) :∀ᶠ x in atTop,∀ (R:BudgetPoint), R.B=highR L x →∀ (c:Side)(N:ℕ)(I V:Type)(Y:Ruby.Hue c N I)(X:Patron.Rail c N V)(a:ℝ), Quits X R.B 1 (taxK L x 3) (rK+rK) a → Purchases Y R.threshold R.B (rK+rK+1) 1 a →Quits (Ruby.Trail Y X R.threshold) R.B 1 (taxK L x 1) rK a :=by
    let f x:=taxK L x 1; let u x:=(f x)⁻¹; let g x:ℝ:=16*(1+(highR L x:ℝ))^4; let m x:= u x+u x*g x; have hU:Rate su L (-1) u:=couplings _ zero_lt_one; have hV:Rate su L 0 g:=(radH L).mul_left 16; have hM: Rate su L (-1) m:=by apply hU.add; simpa only [add_zero] using hU.mul hV
    have hJ:= (((hV.mul hM).mul_right rK⁻¹).mul_left 4).below (by norm_num) (1/2) (by norm_num)
    filter_upwards [framesC L (1/3) (by norm_num),hJ, (hM.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 zero_lt_one] with x hx ht hn R hr c N I V Y X a hp he
    obtain ⟨f',hf,hE⟩:=hp.cost; obtain ⟨b,hb,hQ⟩:=he.paint; have hZ :1 ≤ f x:= Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le); have hu:= zero_lt_one.trans_le hZ
    have hm : (Animals.ballCost R.B:ℝ) ≤ g x:=by unfold g Animals.ballCost; rw [hr]; push_cast; have h0 := pow_le_pow_left₀ (show 0 ≤ (↑(highR L x):ℝ)+↑(highR L x)+1 by positivity) (show (↑(highR L x):ℝ)+↑(highR L x)+1≤2*(1+↑(highR L x)) by linarith) 4; linarith only [h0]
    have hg :0 ≤ g x:=by unfold g; positivity
    have hm':0 < m x:=by unfold m; have h: 0<u x:= inv_pos.mpr hu; positivity
    have hv : 0≤ f':=fun i=>(norm_nonneg _).trans (hE i 1)
    obtain ⟨h₀,h₁⟩:=Ruby.renowned Y X (t:=R.threshold) (fun i=>(norm_nonneg _).trans (hb i 1)) hv hb hE hZ hm' (by norm_num : 0<rK) (by norm_num : 0≤rK) (by norm_num : (1/2:ℝ)<1) (show degreePrice R.B (m x) rK ≤1/2 from (by unfold degreePrice Push.AbsoluteSums.Trees.stretch; refine le_trans ?_ ((le_abs_self _).trans ht); rw [div_eq_mul_inv]; gcongr)) hQ (Ruby.scopes X hu (Real.exp_pos _).le hv hf hZ (by unfold f taxK; rw [← Real.exp_add, ←Real.exp_add]; apply Real.exp_monotone; linarith only [hx.2.1]) hZ) (by rw [mul_one]; exact add_le_add_right (mul_le_mul_of_nonneg_left hm (inv_pos.mpr hu).le) _)
    exact ⟨_,fun i=>budget_loosen (h₁ i) ((le_abs_self _).trans hn),h₀⟩
end YM.QCD.High
