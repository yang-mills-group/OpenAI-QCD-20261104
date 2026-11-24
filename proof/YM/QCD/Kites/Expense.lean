import YM.QCD.Kites.Returns
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Tables
/-! # spending at the OUTPUT of a birth-to-birth handoff
   Use predecessor `x` before the actual birth. Constants respect pre-L position. -/
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
local notation "p0"=>Time.probe S
def convertQ (M L P:ℝ)(N:ℕ):= (2+Time.base su S)*(drains M L P 1 N (Time.probe S))
lemma polynomialH (m l P r a:ℝ)(N:ℕ)(hp:Same S p): billH m l P r N p S.clip S.width S.paths a= convertQ S m l P N *r + Time.top su S*(|a| *p.threshold^3):=by
    unfold billH; simp only []; rw [Time.table su S hp]; unfold convertQ drains scoreT lower Quotes.preExponent; rw [hp.2.2]; simp only [Time.probe]; ring
lemma feeCu (hB:p.B=B)(hs:Same S p)(K Era:ℝ): lower r t (K*Era) p N= lower r t K (p0) N *Era:=by unfold lower Quotes.preExponent Time.probe; simp only [hs.2.2]; ring
lemma pricedE (m l P r:ℝ)(h:0≤ m)(he:0≤ l)(hx:0≤ P)(ht:0 ≤  r)(N:ℕ)(S:BudgetPoint): 0 ≤  drains m l P r N S:=by unfold drains scoreT lower; have hN:= μworth (σ:=Quotes.preExponent S) (N:=N); positivity
lemma chippos (N:ℕ)(h:1 ≤  t)(he:1 ≤  w)(hv:1 ≤  P):0≤ convertQ S t w P N:=mul_nonneg (by have h:= (base_nonneg su S).1; linarith) (pricedE t w P 1 (zero_le_one.trans h) (zero_le_one.trans he) (zero_le_one.trans hv) zero_le_one N (p0))
lemma dawn (L:Side)(t P D:ℝ)(h:0<P):∀ᶠ x:ℝ in atTop,
   |D*fiery su x L^3| ≤ P*Jets.Touch.chip L x:=by
   have hp:= ((Rate.flame (G:=su) (L:=L)|>.pow 3).mul_left D).mul (top_chip L)
   filter_upwards [hp.below (by norm_num) P h, event_chip L 0] with x hx ht
   rw [← div_eq_mul_inv,abs_div,abs_of_pos ht.2.1, div_le_iff₀ ht.2.1] at hx; exact hx
lemma under (L:Side) (K v:ℝ)(hv:0<v)(hk:0<K):∀ᶠ x :ℝ in atTop, K*chip L x≤ v*fiery su x L^2:=by
    filter_upwards [Delay.shift_pos su L,(Touch.Seat.your L).eventually_ge_atTop (K/v)] with x hx h
    have hK:= Delay.monitor_pos su L x; have hp:0 < (betaF su x L):=hx; unfold Touch.chip fiery temp; let p:=pra L x; let S:=betaF su x L
    change K*(S⁻¹*p) ≤ v*( (Real.sqrt S)⁻¹*p )^2; rw [mul_pow, inv_pow,Real.sq_sqrt hp.le]; have hs : K ≤ p*v:= (div_le_iff₀ hv).mp h
    have hh:=mul_le_mul_of_nonneg_right hs (mul_nonneg (inv_pos.mpr hp).le hK.le); exact hh.trans_eq (by ring)
lemma radH (L:Side) : Rate su L 0 (fun x=> (1+(radiusB (betaF su x L) :ℝ))^4):=by
    apply Rate.weaken (Rate.pow ((Rate.const _).add ?_) _) (by norm_num)
    -- price by Delay bill
    refine Rate.compare (Rate.bill.mul_left (G:=su) (L:=L) 1) (Eventually.of_forall fun x=>?_); rw [abs_of_nonneg (Nat.cast_nonneg _),one_mul]; apply le_trans _ (le_abs_self _); unfold radiusB; apply (Nat.ceil_lt_add_one (by positivity)).le.trans; unfold Delay.bill; linarith [show 0 ≤ (radiusB x:ℝ) by positivity]
noncomputable def handQ (B:ℕ)(M:ℕ)(F A C:ℝ):= payment 1 B M 1 A C (S.supportExponent+1) F
lemma hunger (M:ℕ)(J:ℝ)(t:ℝ)(h:0 ≤ t)(x:ℝ)(he:0 ≤ x) (B:ℕ):payment 1 (4*B+2) M 1 t x (S.supportExponent+1) J ≤ (1+B:ℝ)^4*handQ S 6 M J t 1*x := by
    let p:= S.supportExponent+1; have hx:0 ≤ p:=by unfold p; linarith [S.price_pos];
    unfold handQ payment degreeIncome; let g:= (1-Real.exp (-(1:ℝ)))⁻¹; have hg:0≤g:=inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))
    have hB : (Footprint.spread 1 (4*B+2):ℝ)≤ (Footprint.spread 1 6:ℝ) * (1+B:ℝ)^4:=by unfold Footprint.spread Animals.ballCost; push_cast; norm_num; rw [show (28561:ℝ)=(13:ℝ)^4 by norm_num, ←mul_pow]; gcongr; linarith
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (show 0 ≤Real.exp (p*J)*x*t from by positivity)) (by positivity)) hg).trans_eq; unfold p g; ring
lemma banca (hP:1 ≤ P)(hm:1 ≤ r)(hl:1 ≤ u) (L:Side) (K D:ℝ)(hk:0<K)(hD:0<D)(N:ℕ):∀ᶠ x:ℝ in atTop,∀ (p:BudgetPoint), Same S p→p.B=radiusB (betaF su x L) → p.threshold= fiery su x L →∀ θ,|θ| ≤D → bankH r u P (K*chip L x) N p S.clip S.width S.paths θ ≤1:=by
    let A:=lower u P K (p0) N; let Z:=drains r u P K N (p0); let P':= Time.softCeiling su S D; let H:= handQ S 6 0 0 1 1; let C:= handQ S 6 0 81 (1+r) 1
    have hc:0≤Z:=pricedE r u P K (by linarith) (by linarith) (by linarith) hk.le _ _
    have ha:0 ≤ A:=by unfold A lower; have he:=μworth (σ:=Quotes.preExponent (p0)) (N:=N); positivity
    let s x:= (1+(radiusB (betaF su x L):ℝ))^4; have hs : Rate su L 0 s:=radH L; have hv(D): Rate su L (-1/2:ℝ) (fun x=> D*s x*chip L x):= ((hs.mul_left D).mul (chip_rate L)).weaken (by norm_num); have h: Rate su L (-1/2:ℝ) (fun x=> (A*H)*s x*chip L x+(C*(K+A)*s x*chip L x+P'*s x*fiery su x L)):= (hv _).add ((hv _).add ((Rate.mul (hs.mul_left P') Rate.flame).weaken (by norm_num)))
    filter_upwards [h.below (by norm_num) 1 zero_lt_one, under L (max 1 Z) 1 zero_lt_one (lt_of_lt_of_le zero_lt_one (le_max_left ..)),event_chip L 0] with x hx hk hX p hE hp hQ v hw
    let d:=chip L x; have hL:0<d:=hX.2.1; have hz : lower u P (K*d) p N=A*d:=feeCu S hp hE ..
    have hf : drains r u P (K*d) N p=Z*d:=by unfold Z drains scoreT; rw [hz]; unfold A Quotes.preExponent Time.probe; rw [show p.supportExponent= S.supportExponent from hE.2.2]; ring -- inspect
    have he:Z*d≤p.threshold^2:=by rw [hQ]; rw [one_mul] at hk; exact (mul_le_mul_of_nonneg_right (le_max_right ..) hL.le).trans hk
    have hh := soft_table su S hE hw (mul_nonneg hc hL.le) he; rw [hp,hQ] at hh -- dependent p! may unfold left
    apply le_trans ?_ ((le_abs_self _).trans hx)
    unfold bankH; dsimp only []; rw [hz,hf,hp,hE.2.2]; let B:=radiusB (betaF su x L)
    apply (add_le_add (hunger S 0 0 1 zero_le_one (A*d) (mul_nonneg ha hL.le) B) (add_le_add (hunger S 0 81 (1+r) (by linarith) (K*d+A*d) (by positivity) B) hh)).trans_eq; unfold H C P' s B d; ring
end YM.QCD.Kites
