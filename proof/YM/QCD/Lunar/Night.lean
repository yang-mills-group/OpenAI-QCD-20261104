import YM.QCD.Lunar.Mare
/-! # Fermi canonical global Moment. native. -/
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
local notation "Up"=>localW
lemma cards (E:Gem c N I)(hp:Crossing E)(hv:Licence p θ A t E)(ht:0 ≤θ)(h:0<t)(j:Bool): HasSum (fun i:I=>valueB j (Stew.lane E β i)) ((Fintype.card (Site c):ℝ)*valueB j (till E β 0)):=by
    obtain ⟨s,hs,hP⟩:=hv.zone; have hv':=Licence_g hv; have hh(i):= costsE E β (Loom.sumRide _ _ _ hs (fun i=>(hP i).travel) ht) h (fun i=>(hP i).sizeU 1 (flat_ok ..)) i;
    have he : HasSum (lane E β) ((Fintype.card (Site c):ℝ) • (till E β 0)):=by
         apply tendsto_pi_nhds.2; intro k
         simp_rw [Finset.sum_apply]; change HasSum (fun i=> lane E β i k) ((Fintype.card (Site c):ℝ) • (till E β 0 k));
         have hl i: (till E β i)=till E β 0:=plums E β hv' hp hh i
         have hb : (Fintype.card (Site c):ℝ) • (till E β 0 k) =∑ i:Site c,till E β i k:=by simp_rw [fun i=> hl i]; rw [sum_const,card_univ,Nat.cast_smul_eq_nsmul]
         have hy(i:Site c):= (concession E β (hh k) i).hasSum
         rw [hb]; exact (hasSum_sum (s:=univ) fun i _=>hy i).congr_fun fun j=> by simp [unitM]
    rw [show _*valueB j (till E β 0)= valueB j ((Fintype.card (Site c):ℝ) • till E β 0) from (map_smul (valueB j) ..).symm]; exact (valueB j).hasSum he
omit c
open Lunar
set_option maxHeartbeats 600000 in
lemma axes (j:Bool)(h:1<θ)(he:0<t)(p:BudgetPoint)(Q:ℝ):∀ᶠ c:Side in atTop,∀ (I: Type)(E: Gem c N I), Licence p θ Q t E →Crossing E→
    |unitF j c (meter β (Patron.total E p.threshold 1))- valueB j (till E β 0)| ≤ Φ p.B (-(θ-1/4)) c :=by
    obtain ⟨T,hT,H⟩:= defend
    let R (c:Side):= ‖bb j‖*T*((c.val:ℝ)^9*(1/t^2)); have hp(c:Side):=Nat.cast_pos (α:=ℝ)|>.mpr c.pos
    let K(c:Side):=Φ p.B (-θ) c
    have hh : Tendsto (fun (c:Side)=>R c*|Q| *Φ p.B (-(1/4:ℝ)) c) atTop (𝓝 0):= by
       refine (Lunar.shine p.B (show 0<(1/4:ℝ) from by norm_num) 9 (‖bb j‖*T*(1/t^2)*|Q|) (by positivity)).congr (fun i=>?_); unfold R; ring
    filter_upwards [hh.eventually_le_const zero_lt_one] with c hz I E hL he'
    obtain ⟨s,hs,hx⟩:= hL.zone; let V:=labelB j c; let f(i):=V (meter β (letters E p.threshold 1 i)); let g i:= valueB j (Stew.lane E β i); let N:ℝ:= Fintype.card (Site c);
    have hv:0 < N:=by unfold N; positivity
    let bad i:=¬Nonwrapping (E.addr i).support (E.addr i).site; let p' i:= if bad i then s i else 0
    have hb : SumBudget p' (N*(K c*Q)):=by
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
    have hD: SumBudget (fun i=>|f i-g i|) (R c*(N*(K c*Q))):=by
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
    rw [show R c*(N*(K c*Q))/N= R c*(K c*Q) from (by field_simp)] ; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self Q) (Real.exp_pos _).le) hr)
    have hx : K c= Φ p.B (-(1/4)) c * Φ p.B (-(θ-1/4)) c:=by unfold K Φ; rw [←Real.exp_add]; ring_nf
    change R c*(K c *|Q|) ≤ _; rw [hx]; let g:=Φ p.B (-(θ-1/4)) c; nlinarith only [mul_le_mul_of_nonneg_right hz (show 0≤g from (Real.exp_pos _).le)] -- check
end pays
end Project
end YM.QCD.Stew
