import YM.Mills.Glove
/-! # Dynamic rewards. Parametric in supports and count conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z η : ℝ} {i m:ℕ}{f g: ℝ→ℝ}
-- Poll opposition for any impure coefficient. logarithmic rather than catalytic.
def lantern (L:Side)(x:ℝ):=betaF su x L^(1/8:ℝ)
def fundsL (L:Side)(θ x:ℝ):= fan L (-θ) x
-- θ < 1/8 already.
def chipV (L:Side) (x:ℝ):= fan L (-2) x
def stipend (L:Side)(F m l:ℕ)(θ u η C q w ε x:ℝ):= terraceFee F (radiusB x) m (radiusB x) l L q u η w ε (lantern L x) (fan L θ x) (C*fan L θ x)
def request (L:Side)(F m l:ℕ)(θ u η C q w ε p x:ℝ):= stipend L F m l θ u η C q w ε x+(1*Real.exp 1*rem L m (radiusB x) w (chipV L x) p + rust L θ x*rem L m (radiusB x) w 1 p)
lemma beat (L:Side)(F m l:ℕ)(θ u η C q w ε:ℝ)(hu:η < u): Seat L (-2*θ) (stipend L F m l θ u η C q w ε):=by
    let z x:= Real.exp (-(u-η)*fossil (radiusB x) l); let H x:= lantern L x; let t x:= rem L m (radiusB x) w 1 ε
    have hz: Rate su L (-1) z := pale u η hu l
    have hp: Rate su L (1/8) H:= Rate.power
    have hf: Rate su L (1/8+(0+ -1)) (fun x=>H x*(t x*z x)):=hp.mul ((Seat.ruled (earned m w ε)).mul hz)
    have hc (θ) : Seat L θ (fun x=> H x*(t x*z x)):=Seat.eliminated hf (by norm_num)
    let D x:=fan L θ x; let F₁:= fingers F
    have hP:Seat L (-2*θ) (fun x=> F₁^2*(D x)⁻¹^2*(t x*q + (H x*(t x*z x))*q)):= ((((skin_i L θ).powered 2).timesL (F₁^2)).ponies (((earned m w ε).times q).comb ((hc 0).times q))|>.above (by push_cast; linarith))
    have hx:= (hP.comb ((hc (-2*θ)).times (2*q*C*F₁^2))).timesL (Real.exp 1)
    refine hx.equal (Eventually.of_forall (fun x=>?_)); change terraceFee F _ m (radiusB x) l L q u η w ε (H x) (D x) (C*D x)=_
    unfold terraceFee; rw [mul_assoc C, mul_inv_cancel₀ (fan_pos ..).ne',mul_one, leeway L q, leeway L (_*q)]; -- args? explicit order from earlier
    rw [leeway L (_*2*q)]; dsimp only [z,D,H,F₁,t]; ring
lemma sale (L:Side)(F m l:ℕ)(θ u η C q w ε p:ℝ)(ht:θ<1/8)(hu:η < u): Seat L (-2*θ) (request L F m l θ u η C q w ε p):=by
    have h: Seat L (-2*θ) (chipV L) := Seat.keeps.above (by linarith)
    exact (beat L F m l θ u η C q w ε hu).comb (((refunded m w p h).timesL (1*Real.exp 1)).comb ((chip_r L θ).ponies (earned m w p)|>.above (by linarith)))
lemma tollM (L:Side)(θ : ℝ)(F:ℕ)(C :ℝ)(hc:0<C):∀ᶠ x in atTop, ∀ d : ℕ,0<d→
    cashM L θ x * taxK L x (1/2)^d*C^(Cove.kappa (radiusB x +1) F*d) ≤ rust L θ x *taxK L x (7/8)^d:=by
  filter_upwards [zealous L F C hc,upperTax L (1/8) (by norm_num) _ _ (top_chip L), Delay.shift_pos su L] with x hx h H d hd
  let P p:= taxK L x p; have he i:0 < P i:= Real.exp_pos _
  have hi:1 ≤ P (1/8):= Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)
  have hz:=healthy_chip H
  unfold cashM; rw [mul_assoc (rust L θ x), mul_assoc (rust L θ x)]; apply mul_le_mul_of_nonneg_left _ (by unfold rust; positivity)
  rw [pow_mul]; apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_right (h.trans (le_self_pow₀ hi hd.ne')) (pow_nonneg (he _).le _)) (pow_le_pow_left₀ (pow_nonneg hc.le _) hx _) (pow_nonneg (pow_nonneg hc.le _) _) (mul_nonneg (pow_nonneg (he _).le _) (pow_nonneg (he _).le _))) -- check le_self_pow0
  change P (1/8)^d*P (1/2)^d *P (1/4)^d ≤ P (7/8) ^ d; rw [← mul_pow,← mul_pow,show P _ * P _*P _ = P (7/8) from ?_] -- binder ambiguous
  unfold P taxK; rw [← Real.exp_add, ← Real.exp_add]; ring_nf

lemma benefit (L:Side){θ C:ℝ}(hc:1≤C)(F:ℕ):∀ᶠ x in atTop, 1 ≤ lantern L x ∧ ∀ r:ℕ,0<r→lantern L x * taxK L x (1/2)^r * C^(Cove.kappa (radiusB x+1) F *r) ≤ rust L θ x *taxK L x (7/8)^r:=by
    have he : (∀ᶠ x in atTop, lantern L x ≤ cashM L θ x):=by
        have h : Rate su L (1/8) (lantern L):=Rate.power
        filter_upwards [(h.mul (cash_h L θ)).below (by norm_num) 1 zero_lt_one,event_chip L θ] with x hg ht
        have hp:lantern L x/cashM L θ x ≤1:= by rw [div_eq_mul_inv]; exact (le_abs_self _).trans hg
        exact (div_le_one (zero_lt_one.trans_le ht.2.2.2)).1 hp
    filter_upwards [(Work.E09.betaF_growth su L).eventually_ge_atTop 1,he,tollM L θ F C (by linarith)] with x h hs hp
    exact ⟨Real.one_le_rpow h (by norm_num),fun r hr=>((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (by unfold taxK; positivity)) (by positivity)).trans (hp r hr))⟩
lemma sponsorship (L:Side)(F m l:ℕ)(θ u η C q w ε p:ℝ)(ht:θ<1/8)(hu:η < u)(hw:0<θ):∀ᶠ x in atTop, 0< fundsL L θ x ∧ request L F m l θ u η C q w ε p x≤ fundsL L θ x ∧ degreePrice (radiusB x) (fundsL L θ x) 1≤ 1/2:=by
    let H x:=fundsL L θ x; have hf:Seat L 0 (fun x=>(ballCost (radiusB x):ℝ)):=by simpa only [one_mul] using expensed (L:=L) 0 1 0
    have hg: Seat L (-θ) (fun x=> degreePrice (radiusB x) (H x) 1):=by unfold degreePrice stretch; simp only [div_one]; exact ((hf.ponies Seat.keeps).timesL 4 |>.above (by linarith))
    filter_upwards [sale L F m l θ u η C q w ε p ht hu (-θ) (by linarith),hg.shrinks (by linarith) (show 0 < (1/2:ℝ) from by norm_num)] with x he h using ⟨fan_pos ..,(le_abs_self _).trans he,(le_abs_self _).trans h⟩
lemma Fill.cheap (c:Side){D J:Type}(X:Rise c F D J)(W:D→ℝ)(Y:J→ℝ)(h:Fill X W Y a b u v x i)(hq:0≤Y)(hp:0≤ε) (he:ε ≤ u): Fill X W Y a b ε v x i:=by
    refine ⟨h.bud,hp,h.χ, Labels.raise_prices _ _ (fun i=>mul_nonneg (hq i) (pow_nonneg hp _)) h.ε fun i=>mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp he _) (hq i)⟩
end YM.QCD.Jets.Touch
#print axioms YM.QCD.Jets.Touch.sponsorship
#print axioms YM.QCD.Jets.Touch.benefit
