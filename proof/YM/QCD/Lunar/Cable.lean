import YM.QCD.Lunar.Swan
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
section phi
variable {Y Q:Pot G c}{t':ℝ}
lemma drift (a:Pot G c)(b:ℝ): glow P β G (-a) b= -glow P β G a b:=by rw [← neg_one_smul ℝ a, glow_scale]; simp
lemma saint (A B:Pot G c)(t:ℝ): glow P β G (A-B) t=glow P β G A t-glow P β G B t:=by rw [sub_eq_add_neg,glow_plus,drift,sub_eq_add_neg]
lemma subPulse (hp:PulseS P β G Y t u v)(ht:PulseS P β G Q t' A B): PulseS P β G (Y-Q) (t-t') (u+A) (min v B):=by
    refine ⟨lt_min hp.upT ht.upT, fun i hi=> ?_⟩; rw [saint,show glow P β G Y i- glow P β G Q i-(t-t')=glow P β G Y i-t-(glow P β G Q i-t') from (by ring), add_mul]; apply (abs_sub _ _).trans; exact add_le_add (hp.fees i ⟨hi.1,hi.2.trans (min_le_left ..)⟩) (ht.fees i ⟨hi.1,hi.2.trans (min_le_right ..)⟩)
end phi
variable {A':ℝ} (K:PathData su) (G:Clip) (P:BudgetPoint) (hp:K.Bounds G σ A' t)(hB:P.supportExponent=2)(hC:Decent G P)(hw: Geo.Width P G σ)
open Push.BetaTransport
include hp hC hB hw
lemma pureG (a:ℝ) (ha:0<a):∀ᶠ c:Side in atTop, ∃ z M t:ℝ,(1/2:ℝ) ≤ z∧PulseS P β su (kinetic K G P (n:=c)) z M t:=by
    let r:=regularNeed su P G σ A' 0 (P.threshold^2)
    have hh:Tendsto (Φ P.B (-(7/4:ℝ))) atTop (𝓝 0):=by simpa only [pow_zero,mul_one] using shine P.B (show 0 < (7:ℝ)/4 from by norm_num) 0 1 zero_le_one
    filter_upwards [hh.eventually_le_const (by norm_num : (0:ℝ)<1/2),continueS.eventually_gt_atTop 20, keeps β P ha r 0] with c ht hc hT
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
    obtain ⟨w,hw⟩:=height simple β P c; have hh': Y ≤ 1/2:=by apply (le_abs_self _).trans (hα.trans _); convert ht using 1; norm_num
    have ht' := subPulse β hΨ hR; refine ⟨1-Y,M+t,min w (min W s), by linarith, immigrate ht' (lt_min hw.1 ht'.upT) (min_le_right ..) ?_⟩
    intro u hu; exact pulseAgree P.threshold_le hz (show Lab0 su c P β w from hw) ⟨hu.1, hu.2.trans (min_le_left ..)⟩ -- equality of function eta
end Ring0
end YM.QCD.Lunar
#print axioms YM.QCD.Lunar.Ring0.pureG
