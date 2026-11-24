import YM.QCD.Jets.Ellis
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics
/-! # pressure at a variable monitor using fixed AFTER-L budgets. Rate between monitor powers, strictly cheaper than B. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{L:Side} {x u v a b c ν C D T θ: ℝ} {i j:ℕ}{f g: ℝ→ℝ}

-- hats all bets per **coarse variable** x
abbrev pra (L:Side) (x:ℝ):= Delay.fineMonitor su L x
def Seat (L:Side)(a:ℝ)(x:ℝ→ℝ) := ∀ b>a, ∀ᶠ y in atTop, |x y| ≤ pra L y ^ b
namespace Seat
lemma your (L : Side): Tendsto (pra L) atTop atTop:=by
  let f:= fun x=> Real.log (Real.log (betaF su x L)); have hh:Tendsto f atTop atTop:= Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth su L))
  exact Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (α:=ℝ) (show 2≠0 from by norm_num)).comp hh) -- name
lemma keeps : Seat L a (fun x=> pra L x ^ a):=by
    intro b hb; filter_upwards [(your L).eventually_ge_atTop 1] with x h using (abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans h) _)).trans_le (Real.rpow_le_rpow_of_exponent_le h hb.le)
lemma numbers (x : ℝ): Seat L 0 (fun _=> x):= fun b hb=> ((tendsto_rpow_atTop hb).comp (your L)).eventually_ge_atTop _
lemma compares (h: Seat L a f)(hp:∀ᶠ x in atTop, |g x|≤ |f x|): Seat L a g:=by intro b hb; filter_upwards [hp,h b hb] with x h v using h.trans v
lemma equal (h:Seat L a f)(hp:g=ᶠ[atTop] f): Seat L a g:=h.compares (hp.mono fun x hx=> by rw [hx])
lemma above (h:Seat L a f) (he:a≤b): Seat L b f:=fun _ hh=> h _ (he.trans_lt hh)
lemma ponies (h:Seat L a f)(k:Seat L b g): Seat L (a+b) fun x=> f x*g x:=by
   intro v hv; let d:=(v-(a+b))/2; have he:0<d:=half_pos (sub_pos.mpr hv)
   filter_upwards [h (a+d) (by linarith), k (b+d) (by linarith)] with x hx hy
   have hh : a+d+(b+d)=v:=by unfold d; ring
   rw [abs_mul, ← hh, Real.rpow_add (Delay.monitor_pos su L x)]
   exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
lemma times (h:Seat L a f)(x:ℝ): Seat L a (fun y=>f y*x) := add_zero a ▸ (h.ponies (numbers x))
lemma timesL (h:Seat L a f)(x:ℝ): Seat L a (fun y=>x*f y) := zero_add a ▸ ponies (numbers x) h -- ponies
lemma comb (h:Seat L a f)(k:Seat L a g):Seat L a (fun x=> f x+g x):=by
  intro v hv; let d:=(v-a)/2; have he:0 < d:=half_pos (sub_pos.mpr hv)
  have hu:a+d+d=v:=by unfold d; ring
  filter_upwards [h (a+d) (by linarith), k (a+d) (by linarith),((tendsto_rpow_atTop he).comp (your L)).eventually_ge_atTop 2] with x HX H hp
  refine ((abs_add_le ..).trans (add_le_add HX H)).trans ?_ ; rw [← hu,Real.rpow_add (Delay.monitor_pos su L x) (a+d) d,← mul_two]; exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (Delay.monitor_pos su L x).le _)
lemma powered (h:Seat L a f)(n:ℕ): Seat L (a*n) (fun x=> f x^n):=by
  induction n with
  | zero=> simpa using numbers (L:=L) (1:ℝ)
  | succ n ih=>simpa only [pow_succ,Nat.cast_succ,mul_add,mul_one] using ih.ponies h

lemma eliminated (h:Rate su L a f)(hp:a<0): Seat L b f:=by
  intro v hv
  have hh:= (h.mul (Rate.rpow_monitor (-v))); rw [add_zero] at hh
  filter_upwards [hh.below hp 1 zero_lt_one] with x he
  rw [Real.rpow_neg (Delay.monitor_pos ..).le, ← div_eq_mul_inv, abs_div, abs_of_pos (Real.rpow_pos_of_pos (Delay.monitor_pos ..) _), div_le_iff₀ (Real.rpow_pos_of_pos (Delay.monitor_pos ..) _),one_mul] at he; exact he
lemma ruled (h:Seat L a f) : Rate su L 0 f:= (Rate.rpow_monitor (a+1)|>.compare ( (h (a+1) (lt_add_one a)).mono fun i hi=> hi.trans (le_abs_self _)))
lemma shrinks (h:Seat L a f)(hp:a < 0)(he:0<D):∀ᶠ x in atTop, |f x|≤ D:=by
   let v:=-a/2; have hh:0<v:=half_pos (by linarith); filter_upwards [h (-v) (by unfold v; linarith), ((tendsto_rpow_atTop hh).comp (your L)).eventually_ge_atTop D⁻¹] with x hx hy; rw [Real.rpow_neg (Delay.monitor_pos ..).le] at hx; exact hx.trans ((inv_anti₀ (inv_pos.mpr he) hy).trans_eq (inv_inv D))
lemma radius : Seat L 0 (fun i=> (radiusB i:ℝ)):=by
   intro b hb; filter_upwards [Delay.monitor_pays su L 1 (show 0 ≤ (1:ℝ) from zero_le_one) hb] with x h
   rw [one_mul,pow_one] at h; rw [abs_of_nonneg (by positivity)]; apply le_trans _ h; unfold Delay.bill; linarith [sq_nonneg (Real.log (betaF su x L))]
end Seat
end YM.QCD.Jets.Touch
