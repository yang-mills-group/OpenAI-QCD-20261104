import YM.QCD.Hearth.Focus
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
namespace Project
open Revolve Flume Quarry
variable (c)
open Entr Port AnalyticBridge.VerifiedReset
open Entr Port AnalyticBridge.VerifiedReset
variable {o x:Site c}{t u δ ε K A B v' α θ:ℝ}{p:BudgetPoint}{I:Type} (β:Flavor N)
section pays
omit c
open Lunar Pressure ConnectedActivityE6
set_option maxHeartbeats 600000 in
lemma axesPanel (j:Bool)(h:1<θ)(L:Side){u Q:ℝ→ℝ}{r k:ℝ}(hu:Rate su L r Q)(hq:Rate su L k (fun x=> (u x)⁻¹)) :∀ᶠ x in atTop,∀ (c:Side) (P:BudgetPoint){t:ℝ}, P.B=radiusB (betaF su x L) → Hearth.vizR (betaF su x L) ≤ c.val → t=u x →0<t →∀ (I: Type)(E: Gem c N I), Licence P θ (Q x) t E →Crossing E→
    |unitF j c (meter β (Patron.total E P.threshold 1))- valueB j (till E β 0)| ≤ Φ P.B (-(θ-1/4)) c :=by
    obtain ⟨T,hT,H⟩:= defend
    have h' : Rate su L (k*2+r) (fun x=> ‖bb j‖*T*(1/(u x)^2)*Q x):= by
        refine Rate.mul (v:=Q) (Rate.congr (Rate.mul_left (hq.pow 2) (‖bb j‖*T)) (Eventually.of_forall fun i=>?_)) hu; simp
    filter_upwards [Hearth.wonderful h' (1/4) 1 9 (by norm_num) zero_lt_one] with x hx c p t ht hc hq he I E hL he'
    let R (c:Side):= ‖bb j‖*T*((c.val:ℝ)^9*(1/t^2)); have hp(c:Side):=Nat.cast_pos (α:=ℝ)|>.mpr c.pos
    let K(c:Side):=Φ p.B (-θ) c
    have hq' := hx c hc; rw [← ht,← hq, abs_mul,abs_of_nonneg (show 0 ≤ ‖bb j‖*T*(1/t^2) from (by positivity))] at hq'
    have hz : R c*|Q x| *Φ p.B (-(1/4)) c ≤1:=by unfold R; linarith only [hq']
    obtain ⟨s,hs,hx⟩:= hL.zone; let V:=labelB j c; let f(i):=V (meter β (letters E p.threshold 1 i)); let g i:= valueB j (Stew.lane E β i); let N:ℝ:= Fintype.card (Site c);
    have hv:0 < N:=by unfold N; positivity
    let bad i:=¬Nonwrapping (E.addr i).support (E.addr i).site; let p' i:= if bad i then s i else 0
    have hb : SumBudget p' (N*(K c*Q x)):=by
       refine Stem.mast E (B:=p) p' ?_ (fun i=>ite_nonneg (hx i).travel le_rfl) (t:=0) le_rfl; intro i; unfold K; apply budget_mono (budget_scale (Real.exp_pos _).le (hs i))
       · intro j; split; exact mul_nonneg (ite_nonneg (hx _).travel le_rfl) (Real.exp_pos _).le; exact le_rfl
       intro k; split
       next hC=> unfold p'; dsimp only; split
                 next hM=> rw [mul_left_comm,← Real.exp_add,zero_mul]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hx _).travel; have he:= Nat.cast_le (α:=ℝ).mpr (toll_top hM (E.addr k).anchor p.B); -- edit
                           nlinarith only [mul_le_mul_of_nonneg_left he (zero_le_one.trans h.le)]
                 next hM=> have hv:=(hx k).travel; rw [zero_mul]; positivity
       next hC=> rw [mul_zero]
    have hf:= permits E hL he (zero_le_one.trans h.le) (1:Grid c)
    have hr:0≤ R c:=by unfold R; positivity
    have hD: SumBudget (fun i=>|f i-g i|) (R c*(N*(K c*Q x))):=by
         refine budget_mono (budget_scale hr hb) (fun i=> abs_nonneg _) (fun i=>?_); unfold p'; have he0(i):letters E p.threshold 1 i=E.view i 1:=masked_eq _ _ _ _ (flat_ok ..)
         by_cases hx':bad i
         · rw [if_pos hx']; have hK: g i=0:=by unfold g; rw [show lane E β i=0 from (funext fun j=> if_neg hx'), map_zero]
           have hg(p q:Pinor) := cash c j β p q (E.view i 1) (E.addr i).site he ((hx i).sizeU _ (flat_ok ..)) -- he shadow
           rw [hK,sub_zero,show f i= bb j (μDir c j (meter β (E.view i 1))) from congr_arg (labelB j c) (congr_arg (meter β) (he0 i))] -- syntax CLM
           apply ((bb j|>.le_opNorm _).trans (mul_le_mul_of_nonneg_left (H _ _ hg) (norm_nonneg _))).trans_eq; unfold R; ring
         rw [if_neg hx',show f i=g i from Eq.trans (show f i=labelB j c (meter β (E.view i 1)) from congr_arg (labelB j c) (congr_arg (meter β) (he0 i))) (μlink c β j (Licence_g hL) i (of_not_not hx')),sub_self,abs_zero,mul_zero]
    have hf' :HasSum f (labelB j c (meter β (Patron.total E p.threshold 1))):= V.hasSum ((meter β).hasSum hf.hasSum)
    have hp': HasSum g (N*valueB j (till E β 0)):=cards c β E he' hL (zero_le_one.trans h.le) he j
    have ht': (unitF j c (meter β (Patron.total E p.threshold 1))-valueB j (till E β 0))=(∑' i,(f i-g i))/N:=by rw [(hf'.sub hp').tsum_eq,sub_div, mul_comm N,mul_div_cancel_right₀ _ hv.ne']; change N⁻¹ * labelB j c _ -_= _; ring
    rw [ht',abs_div,abs_of_pos hv]; refine le_trans (div_le_div_of_nonneg_right (Lunar.Ring0.absoluteR _ hD|>.2) hv.le) ?_
    rw [show R c*(N*(K c*Q x))/N= R c*(K c*Q x) from (by field_simp)] ; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self (Q x)) (Real.exp_pos _).le) hr)
    have hx : K c= Φ p.B (-(1/4)) c * Φ p.B (-(θ-1/4)) c:=by unfold K Φ; rw [←Real.exp_add]; ring_nf
    change R c*(K c *|Q x|) ≤ _; rw [hx]; let g:=Φ p.B (-(θ-1/4)) c; nlinarith only [mul_le_mul_of_nonneg_right hz (show 0≤g from (Real.exp_pos _).le)] -- check
end pays
end Project
end YM.QCD.Stew
