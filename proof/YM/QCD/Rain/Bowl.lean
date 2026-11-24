import YM.QCD.Rain.Harp
import YM.Push.BETA_TRANSPORT.Separation
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
variable {c L:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Acre Rails Jets.Touch Flume
variable {G:Clip}
lemma averages {I:Type} [Fintype I] [Nonempty I] (f:I→ℝ)(h:∀ i, |f i|≤P) : |(Fintype.card I:ℝ)⁻¹ * ∑ i,f i| ≤P:=by
    have hp:0<(Fintype.card I:ℝ):= by positivity
    rw [abs_mul,abs_of_pos (inv_pos.mpr hp)]; apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=>h i)) (inv_pos.mpr hp).le).trans; simp [mul_assoc, ←mul_assoc,inv_mul_cancel₀ hp.ne']
open PathData Push.BetaTransport
local notation "S?"=> (Fintype.card (Site c):ℝ)
lemma frames (K:PathData su)(h: K.Bounds G σ P q)(p:BudgetPoint) (V:Grid c)(α:Face (Per c)): |K.baseTerm G p V α|≤ 2*G.linear + 2*G.direct+(2*P)^2:=by
    let x:=su.chord (faceValue V α); have hv: 0 ≤ x:=by unfold x Gauge.chord; positivity
    have hp:x≤2:= su.chord_le_two _; let t:=p.threshold; have ht:=p.threshold_pos; have he:= p.threshold_le
    have hr:|clipped G t x|≤2*G.linear+2*G.direct:=by
        unfold clipped; split
        · rw [abs_of_nonneg (div_nonneg (mul_nonneg G.quadratic_pos.le (sq_nonneg _)) (by positivity))]; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hp 2) G.quadratic_pos.le,G.tail_pos]
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg G.tail_pos.le ht.le) hv)]; have hx: G.linear*t*x≤ G.linear *1*2:=mul_le_mul (mul_le_mul_of_nonneg_left he G.tail_pos.le) hp hv (mul_nonneg G.tail_pos.le zero_le_one); linarith only [hx,G.quadratic_pos]
    have hh:‖K.ell V α‖ ≤2*P:=by
        have hx:=h.rows α.2; have he i: ‖K.ellTerms α i V‖ ≤ 2*(|(K.row α.2 i).1| * Real.exp (σ*(K.row α.2 i).2.length)):=by
            rw [ellTerms,norm_smul,Real.norm_eq_abs, mul_comm]; exact mul_le_mul (Slot.eval_norm ..) (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (by positivity)))) (abs_nonneg _) zero_le_two
        have hx' :SumBudget (fun i=>‖K.ellTerms α i V‖) (2*P):=budget_mono (budget_scale zero_le_two hx) (fun _=>norm_nonneg _) he -- ok
        exact (norm_tsum_le_tsum_norm hx'.2.1).trans hx'.2.2
    unfold baseTerm; split
    · apply (abs_add_le ..).trans; exact add_le_add hr (by rw [abs_of_nonneg (by positivity : 0 ≤ ‖K.ell V α‖^2/2)]; nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hh 2, sq_nonneg (2*P)])
    rw [add_zero]; exact le_add_of_le_of_nonneg hr (sq_nonneg _)
lemma seenB (K:PathData su)(h:K.Bounds G σ P q)(p:BudgetPoint)(V:Grid c) (x:ℝ)(hx:|x|≤ u): let z:= 2*G.linear + 2*G.direct+(2*P)^2; |K.inChannels G p x V| ≤ u*((Fintype.card (Face (Per c)):ℝ)*z+S? * (24*P))+ S? *(4*q):=by
     intro z; apply averages (fun i=> K.principal G p x _); intro i; unfold PathData.principal; let W:=pull i 0 V; apply (abs_add_le ..).trans
     have he {k:ℕ} (X:ℕ→Atom su k)(t:ℝ) (hi:SumBudget (fun i=> (X i).budget σ) t) (o: Site c): |PathData.atomSeries X p W o| ≤ t* (2:ℝ)^k := atomSeries_chord h.width hi zero_le_two (fun _=>su.chord_le_two _) o
     have hg {I:Type}[Fintype I](f:I→ℝ)(t:ℝ)(hp:∀ i,|f i|≤ t):|∑ i,f i| ≤ (Fintype.card I:ℝ)*t:=by apply (abs_sum_le_sum_abs ..).trans; apply (sum_le_sum fun i _=> hp i).trans; simp
     rw [abs_mul]; apply add_le_add
     · apply mul_le_mul hx _ (abs_nonneg _) ((abs_nonneg _).trans hx); apply (abs_add_le ..).trans; apply add_le_add (hg _ z (frames _ h p W)); exact hg _ _ (fun i=>(abs_add_le ..).trans ((add_le_add (he _ _ h.three i) (he _ _ h.four i)).trans_eq (by ring)))
     exact hg _ _ (fun i=> (he _ _ h.two i).trans_eq (by ring))
open Extra Precision Iteration Lunar.Ring0
lemma second (t:ℝ→ℝ)(k:ℕ)(X:ℕ→ Atom su k)(he:Charged X σ P)(hp:0<σ)(V:Grid c): |Extra.Iteration.action X V|≤ S? * (2^k*P):=by
   unfold Extra.Iteration.action; apply averages; intro i; unfold uncut; apply (abs_sum_le_sum_abs ..).trans
   refine (sum_le_sum (g:=fun _=>2^k*P) (fun j _=> ?_)).trans (by simp only [sum_const,card_univ,nsmul_eq_mul]; rfl)
   let f n:=(X n).unmasked (pull i 0 V) j; refine (absoluteR f ?_).2; refine budget_mono (budget_scale (pow_nonneg zero_le_two _) he) (fun _=>abs_nonneg _) (fun i=> le_trans (Atom.unmasked_bound ..) ?_); rw [mul_comm]; gcongr; exact Atom.lower_budget _ _ hp
open Raft ParcelR
variable {R:ParcelR}
lemma bPerf (Q:ParcelR)(hr:R.Rates η)(K:Clip)(σ x P t:ℝ)(c:Side) (N:ℕ): ∃ C:ℝ,∀ (X:SunR R)(W:PathData su) (B: BudgetPoint) (v:ℝ), W.Bounds K σ P x →|v| ≤ t→∀ U:Grid c, |Finch.scent X.Z.page B W K v 0 N U| ≤ C:=by
    refine ⟨(N:ℝ)*(↑(Fintype.card (Site c)) * (2^2 *(Smoke.expPrice 2 R.t *R.e)))+(t*((Fintype.card (Face (Per c)):ℝ)*(2*K.linear+ 2*K.direct+(2*P)^2) +(Fintype.card (Site c):ℝ)* (24*P))+ ↑(Fintype.card (Site c)) *(4*x)),fun X W B v hp hv V=>?_⟩; unfold Finch.scent Reggae.pulse; rw [zero_mul,zero_sub]; apply (abs_add_le ..).trans; rw [abs_neg,abs_neg,abs_mul,abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤_)]; exact add_le_add (mul_le_mul_of_nonneg_left (second id 2 X.Z.page (X.Z.cost hr.ht) hr.ht V) (Nat.cast_nonneg N)) (seenB _ hp B V _ hv)
end YM.QCD.Rain
