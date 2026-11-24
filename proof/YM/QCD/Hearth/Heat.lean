import YM.QCD.Hearth.Signal
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
namespace Ring0
open Cove StepData Stew Reggae Patron Lat Acre Rails Kites Push.AbsoluteSums Matrix
variable {I:Type} {u₀:Pot su c}{v M θ H K A B d η r α:ℝ}
open Collection PhysicalNext.Repeat WilsonStartup
variable (β:PlaqAxes) {x' v' y':ℝ}
variable {A':ℝ} (K:PathData su) (G:Clip) (P:BudgetPoint) (hp:K.Bounds G σ A' t)(hB:P.supportExponent=2)(hC:Decent G P)(hw: Geo.Width P G σ)
open Push.BetaTransport
include hp hC hB hw
lemma purePanel (a:ℝ) (ha:0<a)(hc:20<c.val)(ht:Φ P.B (-(7/4:ℝ)) c≤1/2)
    (hT:∃ t W:ℝ,∀ (I:Type)(X: Patron.Gem c 0 I), Crossing X → Quartz X → Licence P 2 (regularNeed su P G σ A' 0 (P.threshold^2)) a X → ∃ Y:ℝ,|Y| ≤ Φ P.B (-7/4) c∧ PulseS P β su (gaugeF X P) Y W t) :  ∃ z M t:ℝ,(1/2:ℝ) ≤ z∧PulseS P β su (kinetic K G P (n:=c)) z M t:=by
    let r:=regularNeed su P G σ A' 0 (P.threshold^2)
    obtain ⟨s,t,hX⟩:= hT; let T:= bedT K P c; let D:=vowT K P G c; let X:=ostinato T D 0;
    obtain ⟨hQ,hΩ,hE,hP,hY⟩:= vowsP K G P 0 hp hC hw hc ha
    rw [hB] at hE
    obtain ⟨Y,hα,hR⟩:= hX _ X hQ hΩ hE; obtain ⟨W,M,hΨ⟩:=grace c P simple β hc
    let A: Pot su c :=kinetic K G P
    let Z:Pot su c := fun U=>∑ i,heads P i U; let ZY:Pot su c:= gaugeF X P
    have hz(U)(hu:flags P.threshold U=∅): A U=Z U - ZY U:=by
         have he: ZY U=(T.pours D).additive P U:=by unfold ZY gaugeF; rw [show Patron.total X P.threshold U=(Reggae.ocean c 0) _ from ((hY U).2).tsum_eq, Reggae.taleP]
         have hr(U:Config su c)(hi: flags P.threshold U=∅):∑' i, D.logarithm i U=0:=by
             refine Eq.trans (tsum_congr (g:=fun _=> (0:ℝ)) (fun i=> ?_)) tsum_zero; have h := hP.life; have hξ : (riff T D 0).mean i U=0:=by_contra fun H=> h.non i U H (by simp only [Healthy,hi,Finset.disjoint_empty_right])
             have hh : river c 0 ((riff T D 0).mean i U)= -(D.logarithm i U):=Reggae.toe _
             rw [hξ,map_zero] at hh; linarith
         have ht:=wedgeK K G P hp hC hw hc U; rw [he]; rw [hr U hu,add_zero] at ht; unfold Z; linarith only [ht] -- `A`
    obtain ⟨w,hw⟩:=height simple β P c; have hh': Y ≤ 1/2:=by apply (le_abs_self _).trans (hα.trans _); rw [show (-7/4:ℝ)= -(7/4:ℝ) from (by ring)]; exact ht
    have ht' := subPulse β hΨ hR; refine ⟨1-Y,M+t,min w (min W s), by linarith, immigrate ht' (lt_min hw.1 ht'.upT) (min_le_right ..) ?_⟩
    intro u hu; exact pulseAgree P.threshold_le hz (show Lab0 su c P β w from hw) ⟨hu.1, hu.2.trans (min_le_left ..)⟩ -- equality of function eta
omit hp hC hB hw
variable {L:Side}{f:ℝ→ℝ}
open Hearth Pressure ConnectedActivityE6
-- get gate condition via polynomial
lemma raysR (h:Rate su L a f)(N:ℕ):∀ᶠ x in atTop,∀ (c:Side) (P:BudgetPoint) (u:ℝ),0<u → P.threshold=fiery su x L → P.B=radiusB (betaF su x L) → vizR (betaF su x L) ≤ c.val→ ∃ t W:ℝ,∀ (I:Type)(X:Patron.Gem c N I), Crossing X → Quartz X → Licence P 2 (f x) u X →∃ Y:ℝ, |Y| ≤ Φ P.B (-7/4) c ∧ PulseS P β su (gaugeF X P) Y W t:=by
   have hi : Rate su L 1 (fun x=> 100/(fiery su x L)^2):= by
       have he :∀ᶠ x in atTop, 0< fiery su x L ∧ Jets.Touch.chip L x ≤ fiery su x L ^ 2:=by
           filter_upwards [under L 1 1 zero_lt_one zero_lt_one,Delay.shift_pos su L] with x hx ht; rw [one_mul, one_mul] at hx; refine ⟨mul_pos (by exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) (Delay.monitor_pos su L x),hx⟩
       refine Rate.compare ((Jets.Touch.top_chip L).mul_left 100) ?_; filter_upwards [he, Jets.Touch.event_chip L 0] with x hx hv
       rw [abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _)),abs_of_nonneg (mul_nonneg (by norm_num) (inv_pos.mpr hv.2.1).le), ← div_eq_mul_inv]; exact div_le_div_of_nonneg_left (by positivity) hv.2.1 hx.2
   filter_upwards [wonderful (hi.mul h) (1/4) 1 10 (by norm_num) zero_lt_one] with x hx c P u hu hp ht he
   have hc:=seen _ _ he |>.2; apply keepsPanel β P hu (f x) N (by omega); have hk:=hx c he; rw [← hp,← ht, abs_mul,abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _))] at hk
   apply le_trans (a:=meterP P c*_ * _/_) _ hk; apply le_of_eq; unfold meterP Φ sPer; field_simp
variable {G':Stage}
lemma liftsK (L:Side)(S:Stage)(hP:S.supportExponent=2):∀ᶠ x in atTop,∀ (c:Side) (P:BudgetPoint)(A:PathData su)(u V:ℝ),0<u→ A.Bounds S.clip S.width S.paths V→ Decent S.clip P → Geo.Width P S.clip S.width → Now L P S x → vizR (betaF su x L)≤c.val →∃ z M t:ℝ,(1/2:ℝ)≤z ∧PulseS P β su (kinetic A S.clip P (n:=c)) z M t:=by
    let f (x:ℝ):= Time.base su S*(fiery su x L ^ 2); have hi:= raysR β ((Rate.flame (L:=L) (G:=su)).pow 2|>.mul_left (Time.base su S)) 0
    filter_upwards [hi, wonderful (Rate.const (L:=L) (G:=su) 1) (7/4) (1/2) 0 (by norm_num) (by norm_num)] with x hx hX c B A u V hu ha hb hQ h hΞ
    have hv:= (seen _ c hΞ).2
    apply purePanel β _ _ B ha (h.era.2.2.trans hP) hb hQ u hu (show 20 < c.val from hv) _
    · rw [Time.table su _ h.era]; simp only [abs_zero,zero_mul,mul_zero,add_zero,h.baseG]; exact hx c B u hu h.baseG h.ball hΞ -- dependent rw problem
    rw [h.ball]; simpa only [abs_one,pow_zero,mul_one] using hX c hΞ
end Ring0
end YM.QCD.Lunar
