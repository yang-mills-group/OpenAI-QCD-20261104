import YM.Clink.Ballet
import YM.Clink.Awe
/-! Combined bloom post. Actual width t theta and full width ξ separately.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ C C' α α' ξ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder
open Metric
variable {I:Type}
-- Mask on Bloom per reference. Need rents financial & bounds proportional to t
local notation "Ω" x:arg=> tribute B b n x
local notation "rT" x:arg=> Run.rent σ B x
variable (W:Bloom k)(i j:Walk)(o:Site c)
local notation "x'"=> stop o i
local notation "y'"=> stop (x') j
local notation "N'"=> nursery W i j o
lemma faresT (he:0<t)(hH:2*t=a)(ht: 0≤η)(hu:η/B≤ t)(hρ:0<B)(hk:i.length+j.length≤1+W.tail.length) : rent η B N'*W.price ≤ Real.exp (η*(3+2*(k:ℝ))+2*t)*W.paid a:=by
        unfold Bloom.paid; have he':t≤a:=by linarith
        have huL:(twig W).length+(i.length:ℝ)+(j.length:ℝ) ≤ (W.span:ℝ)+1:=by
              have hv: (i.length:ℝ)+j.length ≤1+(W.tail.length:ℝ):=by exact_mod_cast hk
              unfold Bloom.span twig Atom.length; push_cast; linarith
        rw [← mul_assoc (Real.exp _)]
        apply mul_le_mul_of_nonneg_right _ W.price_nn; rw[← Real.exp_add]; apply (expense W i j o hρ ht hu).trans; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left huL he.le, mul_le_mul_of_nonneg_right he' (Nat.cast_nonneg (α:=ℝ) W.span),he]
lemma subsidy (a σ:ℝ)(b n k:ℕ)(ha:0<a)(hσ:0≤σ)(hk:0<k): ∃ B:ℕ,∃ C Q δ:ℝ,1 ≤ Q∧0<δ∧0 ≤ C∧∀ (ξ:ℝ), 0 < ξ → ξ ≤1 →∀ (c:Side)(p:BudgetPoint),p.threshold≤δ*ξ→p.power ≤ b→p.order ≤ n→B≤p.B →∀ (x:Site c) (I:Type) (W:I→Bloom k)(r:ℝ) (H:Fractal W a r) (i j:I→Walk)(o:I→Site c), (∀ s,List.length (i s)+List.length (j s) ≤ 1 + List.length (W s).tail) → (∀ s,x∈ nursery (W s) (i s) (j s) (o s)) → StrongR x (fun U:Grid c=>∑' s:I, blockL (o s) (stop (stop (o s) (i s)) (j s)) (episode (W s) (i s) (j s) (o s) ξ (settled U))) p σ (C*r*ξ) (Q*C*r*p.threshold) :=by
        let u:=a/2; have hu:0<u:=half_pos ha; let ε:=σ+1; have hε:0<ε:=by unfold ε; linarith
        obtain ⟨P,δ,hP,hD,h⟩:= skiff u hu; let d:= min δ (min 1 (Real.exp u-1)); have hd:0 < d:=lt_min hD (lt_min zero_lt_one (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)))
        have hd':d ≤1:=(min_le_right ..).trans (min_le_left ..)
        obtain ⟨B,hB'⟩:=exists_nat_gt (ε/u); have hb:0 < (B:ℝ):= (div_pos hε hu).trans hB'
        have hσ': ε/B≤u:=by apply (div_le_iff₀ hb).mpr; linarith only [(div_lt_iff₀ hu).mp hB']
        obtain ⟨K,hK,H⟩:= applause B b n; obtain ⟨E,hE,hG⟩:= polarBudget n b B
        let V:= Real.exp (ε*(3+2*(k:ℝ))+2*u); let Z:= V*‖TouchL‖^2*P^k; let T:= max (K*V) (K*Z); let M:=1+ E/d
        have hM : 1 ≤ M:=le_add_of_nonneg_right (by positivity)
        have hT:0≤T:=(mul_nonneg (zero_le_one.trans hK) (Real.exp_pos _).le).trans (le_max_left ..)
        refine ⟨B,T, M,d,hM,hd,hT,fun ξ hξ hξ' c p hθ hp hN hx x I W r h₁ i j o h2 hx0=>?_⟩
        let f:= d/ξ; have hv : f*ξ^2=d*ξ:=by unfold f; field_simp
        have hγ: 0 < d*ξ:=mul_pos hd hξ
        have hδ:d*ξ≤ d:=mul_le_of_le_one_right hd.le hξ'
        have hμ:Bottle u P f ξ:=by
              refine ⟨fun n W v Z h₀ i=>?_⟩; rw [hv] at h₀; have hβ: Kingdom n (d*ξ) ⊆Kingdom n (δ*ξ):=Set.iUnion_mono fun _=> Metric.ball_subset_ball (mul_le_mul_of_nonneg_right (min_le_left ..) hξ.le)
              exact h ξ hξ hξ' n W v Z i (hβ h₀)
        have hPS: Forum (c:=c) p b n B (d*ξ) E:= ⟨hθ,hx,hp,hN,hE,fun _ _ o₁ _ _ F h h₀ X l hn hy hq=> hG c _ p F o₁ _ _ _ _ h h₀ hp hN hθ (hδ.trans hd') l hn hy hq X⟩
        let U(s):= nursery (W s) (i s) (j s) (o s); let X(s):=episode (W s) (i s) (j s) (o s) ξ; let f0(s):= (W s).price*p.threshold; let f1(s):=harvestK (W s) (i s) (j s) u P ξ; let y(s):=stop (stop (o s) (i s)) (j s)
        let v:=p.threshold; have hN (s:I): StockR (o s) (y s) (U s) p (X s) (d*ξ) (f1 s) (f0 s):= ⟨influenced _ _ _ _ ξ P f u _ hμ (h₁.sect s) (zero_le_one.trans hP) hξ hγ hu hv.symm (hδ.trans ((min_le_right ..).trans (min_le_right ..))),fun U h=>shadesR _ _ _ _ _ h ξ hξ hk, van _ _ _ _ ξ hξ hk,(mul_nonneg (Bloom.price_nn _) p.threshold_pos.le) ⟩
        let V'(s):=tribute B b n (U s); let A(q:I→ℝ)(s:I):= Run.rent σ B (U s)*(V' s*q s)
        have hz (q':I→ℝ) (l:ℝ)(hl:0 ≤l)(hw:∀ i,0≤q' i) (hp:∀ s, K*(rent ε B (U s)*q' s) ≤ T*((W s).paid a)*l): ∃ A':ℝ,HasSum (A q') A'∧ A'≤ T*r*l:=by
             have hm(i:I):0≤A q' i := mul_nonneg (Run.fair ..).le (mul_nonneg (by unfold V' tribute; positivity) (hw i))
             have hξ (i:I): A q' i ≤ T*((W i).paid a)*l:=by
                  let Y':=U i; have hhP (V:Support c): Run.rent σ B V*rent 1 B V=rent ε B V:=by unfold ε Run.rent; rw[←Real.exp_add,add_mul,one_mul]
                  refine le_trans ?_ (hp i)
                  change Run.rent σ B Y'*(tribute B b n Y'*q' i)≤ _; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (H c Y') (hw i)) (Run.fair ..).le).trans_eq; rw [← hhP]; ring
             have hA := (h₁.bills.mul_left T).mul_right l; have hV:= Summable.of_nonneg_of_le hm hξ hA; exact ⟨_,hV.hasSum,(hV.tsum_le_tsum hξ hA).trans (by rw [tsum_mul_right,tsum_mul_left]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁.bill hT) hl)⟩
        have hu' (s):0 ≤ (W s).paid a:=(W s).price_nn.trans ((W s).paidUp ha.le)
        have hb0:0 < B:= Nat.cast_pos.mp hb; have hv1:= hz f1 ξ hξ.le (fun i=>(hN i).crop.1) (fun s=> by apply le_trans (mul_le_mul_of_nonneg_left (show _ ≤ Z*_ *ξ from rentC (W s) (i s) (j s) (o s) (P:=P) (σ:=a) (η:=ε) rfl hu (zero_le_one.trans hP) hξ hξ' hk (h2 s) hb0 hε.le hσ') (zero_le_one.trans hK)); rw [←mul_assoc,←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (hu' s)) hξ.le)
        have hv':= p.threshold_pos; have hv0:= hz f0 v hv'.le (fun i=> (hN i).nneg) (fun s=> by unfold f0; rw[←mul_assoc _ (W s).price,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hv'.le; apply (mul_le_mul_of_nonneg_left (faresT (W s) _ _ _ hu (by unfold u;ring) hε.le hσ' hb0 (h2 s)) (zero_le_one.trans hK)).trans; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left ..) (hu' s))
        have Heq:T*r*v + E*(T*r*ξ)*(p.threshold/(d*ξ))= M*T*r*v:=by unfold M v; field_simp
        rw [←show T*r*_+ E*(T*r*ξ)*_= _ from Heq]; exact ringF X f1 f0 o y U (fun s=>⟨(nucleus (W s) ..).1,(nucleus _ _ _ _).2.2,hx0 _⟩) hN hγ hσ hPS _ (fun _=>rfl) hv1 hv0
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.subsidy
