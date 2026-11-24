import YM.QCD.High.Yang
/-!
# A polylog lower requirement on all listening sides
Teller price can be used when c large in terms of this scale.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Hearth
open Function Lattice Wilson Finset Filter RG ConnectedActivityE6 Pressure Push.AbsoluteSums Flume Jets Jets.Touch Lunar Asymptotics
open scoped BigOperators Topology ContDiff Classical
variable {B t k:ℕ}{L c:Side}{ε A d q x a:ℝ}{f g:ℝ→ℝ}
abbrev vizR (x:ℝ):= 128*(1+radiusB x)^2
lemma seen (B:ℕ)(c:Side)(h:128*(1+B)^2 ≤ c.val): B ≤ tollV B c ∧ 21 ≤ c.val:=by
   have hh : 1≤(1+B)^2:= one_le_pow₀ (by omega)
   have hp :128 ≤128*(1+B)^2:=by omega
   refine ⟨?_,by omega⟩; by_contra! hn; have ht:=le_trans h (badS (show 2≤c.val from (by omega)) B); nlinarith
-- exponential dominates even a scale power
lemma paysA (K:ℝ)(h:0<ε)(L:Side):Rate su L K (fun x=> Real.exp (-ε*(radiusB (betaF su x L)))):=by
    intro v hv; let H:=Work.E09.betaF_growth su L; filter_upwards [(Real.tendsto_log_atTop.comp H).eventually_ge_atTop (-v/ε),H.eventually_ge_atTop 1] with x hx hh
    let t:= betaF su x L; have ht:0<t:=zero_lt_one.trans_le hh; let y:=Real.log t; rw [abs_of_pos (Real.exp_pos _),Real.rpow_def_of_pos ht]; apply Real.exp_monotone; apply (mul_le_mul_of_nonpos_left (Nat.le_ceil _) (neg_nonpos.mpr h.le)).trans
    have hs : -v ≤ y *ε:=(div_le_iff₀ h).mp hx; linarith only [mul_le_mul_of_nonneg_right hs (Real.log_nonneg hh)]
lemma siteM (L:Side) :Rate su L 0 (fun x=> 1+(radiusB (betaF su x L):ℝ)):=by
    refine Rate.compare (Kites.radH L) (Eventually.of_forall fun i=>?_); let t:=1+(radiusB (betaF su i L):ℝ); change |t|≤ |t^4|; have ht:1 ≤ t:=by unfold t; simp
    rw [abs_pow]; exact le_self_pow₀ (ht.trans (le_abs_self _)) (by decide)
lemma halts (L:Side)(R:ℕ): ∀ᶠ x in atTop, R ≤ radiusB (betaF su x L):= (Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)).eventually_ge_atTop R
lemma wonderful (h:Rate su L a f)(ε δ:ℝ)(d:ℕ)(hp:0<ε)(hh:0<δ) :∀ᶠ x in atTop,∀ c:Side, vizR (betaF su x L) ≤c.val → Φ (radiusB (betaF su x L)) (-ε) c*(c.val:ℝ)^d*|f x| ≤δ:=by
   let B x:= radiusB (betaF su x L)
   let g x:= Real.exp (-(ε/2)*(B x:ℝ)); have hf :Rate su L (-1-a) g:= paysA _ (half_pos hp) _; have hk:= ((hf.mul (((siteM L).mul_left 100).pow d)).mul h).below (by ring_nf; norm_num) δ hh
   have ht:= (isLittleO_pow_exp_pos_mul_atTop d (half_pos hp)).tendsto_div_nhds_zero; obtain ⟨R,hR⟩:= eventually_atTop.mp ((ht.comp (show Tendsto (fun i:ℕ=>(i:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)).eventually_le_const (show (0:ℝ)<1 from zero_lt_one)) -- edit
   filter_upwards [hk, halts L (max R 1)] with x hx hf c hC
   obtain ⟨hl,ho⟩:= seen _ c hC
   let V:= tollV (B x) c; let X:ℝ:= V; let W:ℝ:= 100*(1+(B x:ℝ)); have ht0:max R 1≤V:=hf.trans hl
   have hh:0<W:=by unfold W; positivity
   have hu:1≤X:=by unfold X; exact_mod_cast (le_trans (le_max_right R 1) ht0)
   have hm: (c.val:ℝ) ≤ X*W:=by
       have hz : (c.val:ℝ) ≤10*(X*((4*B x+2:ℕ):ℝ)+(2*B x:ℕ)):=by unfold X V; exact_mod_cast badS (c:=c) (show 2 ≤ c.val from (by omega)) (B x)
       unfold W; push_cast at hz; nlinarith

   let Z:= Real.exp (-(ε/2)*X); have hz: Φ (B x) (-ε) c=Z*Z:=by rw [←Real.exp_add]; unfold Φ; change Real.exp _=Real.exp (_*(V:ℝ)+_); unfold X; congr 1; ring -- edit
   rw [← show _= radiusB (betaF su x L) from (rfl:B x=_),hz]
   have hx': Z*X^d ≤1 :=by
       have hy := hR V ((le_max_left ..).trans ht0)
       unfold Z; rw [neg_mul,Real.exp_neg,mul_comm,←div_eq_mul_inv]; exact hy
   have he:Z ≤g x:=by apply Real.exp_monotone; exact mul_le_mul_of_nonpos_left (by unfold X V B; exact_mod_cast hl) (by linarith)
   change |g x * W^d * f x| ≤δ at hx; apply le_trans _ hx; rw [abs_mul,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hh.le _))]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
   apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans; rw [mul_pow,mul_assoc Z Z _,←mul_assoc Z (X^d)]; exact (le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx' (by positivity)) (Real.exp_pos _).le) (by simp only [one_mul]; gcongr)) -- let precise
end YM.QCD.Hearth
