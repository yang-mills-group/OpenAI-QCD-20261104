import YM.QCD.Runnel.Puck

/-! # Route expansion group in steps of r; buy arbitrarily narrow exponent at any fixed b -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
abbrev Own (f : Side) := Heritage (id : Site f→Site f) (id : Site f→Site f)
variable {f : Side} {δ b p R : ℝ} {B n r : ℕ}
def gal (δ : ℝ) := 1+‖TouchL‖*δ
lemma step_price (t : Site f) (w : Walk) (U : Pulse f) (h : U∈Kingdom f δ) : ‖plaza t w U‖ ≤ gal δ^w.length:=by
  obtain ⟨P,hP⟩:= Set.mem_iUnion.mp h
  have he : ‖plaza t w (settled P)‖≤1:=by rw [plaza_leg]; exact rotation_price (circle ..)
  have ht : ‖U-settled P‖ ≤ δ:=by rw [Metric.mem_ball,dist_eq_norm] at hP; exact hP.le
  unfold gal; linarith [(norm_sub_norm_le (plaza t w U) _).trans (plazas t w U P (mul_le_mul_of_nonneg_left ht (norm_nonneg TouchL)))]
lemma step_own (t : Site f) (w : Walk) (hb : 0≤b) (hd : 0<δ) (hL : w.length≤r) (hr : 2*r≤B): Own f δ b B (fun U=> routeM t U w) (Pile b (2*r)*gal δ^r):= by
  have he : 1≤gal δ:=by unfold gal; apply le_add_of_nonneg_right; positivity
  refine tiled injective_id injective_id hb hr (pow_nonneg (zero_le_one.trans he) r) (plaza t w) (fun U=>plaza_leg ..) ((membership t w).dilate (show 2*w.length≤2*r by omega))
    (fun U k=>gaugeM ..) (fun U _=> ((smoothM ..).differentiable (by simp)) U) fun U hu=> (step_price t w U hu).trans (pow_le_pow_right₀ he hL) -- syntax
lemma cohorts (t : Site f) (w : Walk) (hb : 0≤b) (hd : 0<δ) (hL : w.length ≤ n*r) (hr : 2*r≤B) (hn : 0<n) : Own f δ b B (fun U=> routeM t U w) ((Pile b (2*r)*gal δ^r)^n):=by
  induction n generalizing w with
  | zero=>omega
  | succ n ih=>
    let C:=Pile b (2*r)*gal δ^r; have hc: 0≤C:=by unfold C; have h:=pile_pos b (2*r); unfold gal; positivity
    by_cases he : n=0; · subst n; simpa only [Nat.zero_add, pow_one] using step_own t w hb hd (show w.length≤r from by simpa using hL) hr
    rw [← List.take_append_drop r w]; simp_rw [appendM]; rw [pow_succ,mul_comm _ (Pile b (2*r)*gal δ^r)]
    exact (step_own t _ hb hd (List.length_take_le ..) hr).meet (ih (w.drop r) (by rw [List.length_drop]; rw [add_mul,one_mul] at hL; omega) (Nat.pos_of_ne_zero he)) hd hb hc (pow_nonneg hc _)
lemma rides_for (t : Site f) (w : Walk) (hb : 0≤b) (hd : 0<δ) (hp : 0<p) (hr : 0<r) (hB : 2*r≤B)
    (hg : Pile b (2*r)*gal δ^r ≤ Real.exp (p*r)): Own f δ b B (fun U=>routeM t U w) (Real.exp (p*r)*Real.exp (p*w.length)):=by
  let n:=w.length/r+1
  have hh : w.length/r*r≤ w.length:=Nat.div_mul_le_self ..
  refine (cohorts (n:=n) t w hb hd (by rw [mul_comm]; exact le_of_lt (Nat.lt_mul_div_succ w.length hr)) hB (by positivity)).mono ?_
  have ht : 0≤gal δ:=by unfold gal; positivity
  apply (pow_le_pow_left₀ (mul_nonneg (pile_pos ..).le (pow_nonneg ht _)) hg n).trans
  rw [← Real.exp_nat_mul, ← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
  unfold n; push_cast; have hs : (↑(w.length/r):ℝ)*r ≤ (w.length:ℝ):=by exact_mod_cast hh
  nlinarith only [mul_le_mul_of_nonneg_left hs hp.le]

lemma tides (C : ℝ) (k : ℕ) (hp : 0<p): Tendsto (fun n:ℕ=> C*(n:ℝ)^k*Real.exp (-p*n)) atTop (𝓝 0):=by
  have he:Tendsto (fun n:ℕ=>p*n) atTop atTop:=tendsto_natCast_atTop_atTop.const_mul_atTop hp
  have hh:= ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp he).const_mul (C/p^k)
  rw [mul_zero] at hh; apply hh.congr
  intro n; simp only [Function.comp_apply,mul_pow,neg_mul]; field_simp
lemma ballad (b : ℝ) (hp : 0<p):∃ r : ℕ,∃ δ : ℝ, 0<r ∧ 0<δ ∧ Pile b (2*r)*gal δ^r ≤ Real.exp (p*r):=by
  have hh : ∀ᶠ n:ℕ in atTop,Pile b (2*n) < Real.exp (p*n):=by
    filter_upwards [eventually_gt_atTop 0,(tides (5^4 * Real.exp b) 4 hp).eventually (gt_mem_nhds (zero_lt_one))] with n hn hh
    have ht : 1≤ (n:ℝ):=by exact_mod_cast hn -- mismatch
    change 5^4*_*_*_<1 at hh; rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv,div_lt_one (by positivity)] at hh
    refine lt_of_le_of_lt ?_ hh
    unfold Pile; push_cast; rw [mul_right_comm]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; rw [← mul_pow]; gcongr; linarith
  obtain ⟨r,hr,H⟩:= (hh.and (eventually_gt_atTop 0)).exists
  have hc : Continuous (fun x:ℝ=>Pile b (2*r)*gal x^r):=by unfold gal; fun_prop
  obtain ⟨δ,h1,h2⟩:= ((hc.continuousWithinAt.eventually (gt_mem_nhds (by simpa [gal] using hr))).and (self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Set.Ioi 0))).exists
  exact ⟨r,δ,H,h2,h1.le⟩
end YM.QCD.Run
