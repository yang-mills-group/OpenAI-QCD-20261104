import YM.Helio.Blade
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
variable (G:Silo c)(x:Axis){T K:ℝ}
variable {I β:Type}
-- for measurement P, preserve analytic base accuracy demands via exposes.Core Budget P. diameter uses B; after welcome norm cap
structure Trust (Z:I→ParcelZ (c:=c))(p:BudgetPoint)(σ T K:ℝ):Prop where
    book:∃ (f g:I→ℝ)(b:I→ℕ), (∀ i, (Z i).Ticket p (f i) (g i) (b i)) ∧ Ac.Hit (fun i=> (Z i).R) p.B f σ T ∧ Ac.Hit (fun i=> (Z i).R) p.B g σ K
namespace Trust
variable {Z:I→ParcelZ (c:=c)}(h:Trust Z p σ T K)
include h
lemma enlarge {A D:ℝ}(hp:T ≤ A)(hq:K≤D): Trust Z p σ A D:=by obtain ⟨f,g,b,h,hp',hg⟩:=h.book; exact ⟨f,g,b,h,fun i=>budget_loosen (hp' i) hp,fun i=>budget_loosen (hg i) hq⟩
lemma duo (R:β→ParcelZ (c:=c))(hp:Trust R p σ a u): Trust (Sum.elim Z R) p σ (T+a) (K+u):=by
    obtain ⟨f,g,b,h₁,h,h'⟩:=h.book; obtain ⟨m,l,n,h₂,H,H'⟩:=hp.book; refine ⟨Sum.elim f m, Sum.elim g l, Sum.elim b n,fun i=>?_ ,fun i=> Extra.Iteration.Cost.sum (h _) (H _),fun i=> Extra.Iteration.Cost.sum (h' _) (H' _)⟩ -- arguments implicit. 
    · cases i; exact h₁ _; exact h₂ _
omit h in
private lemma resize (F:I→ℝ)(hp:0 ≤ t)(he:Ac.Hit (fun i=> (Z i).R) p.B F σ T) : Ac.Hit (fun i=> (Z i).R) p.B (fun i=> t*F i) σ (t*T):=by
    intro i; convert budget_scale hp (he i) using 1; funext j; split <;> rename_i hj; · simp only [if_pos hj,mul_assoc]
    simp only [if_neg hj,mul_zero]
lemma flopX : Trust (fun i=> (Z i).turnover) p σ (‖clapL‖*T) (‖clapL‖*K):=by
    obtain ⟨f,g,b,H,hF,hG⟩:=h.book; refine ⟨_,_,b,fun i=> ParcelZ.turnA (Z i) (H i),fun i=> ?_,fun i=> ?_⟩
    · exact resize f (norm_nonneg clapL) hF i
    exact resize g (norm_nonneg clapL) hG i -- binder T problem
lemma rentsX (s:ℝ): Trust (fun i=> (Z i).rents s) p σ (‖s‖*T) (‖s‖*K):=by
    obtain ⟨f,g,b,H,hF,hG⟩:=h.book; refine ⟨_,_,b,fun i=> ParcelZ.rentA (Z i) (H i) s,fun i=> ?_,fun i=> ?_⟩
    · exact resize f (norm_nonneg s) hF i
    exact resize g (norm_nonneg s) hG i
end Trust
structure Deposits (V:St c)(p:BudgetPoint)(a T K:ℝ): Prop where
    art:∃ (I:Type)(_ :Fintype I)(Z:I→ParcelZ (c:=c)), Trust Z p a T K ∧ V=∑ i,(Z i).val
namespace Deposits
end Deposits
lemma prepaid (B b n:ℕ){r:ℝ}(hK: CreditBeam r)(hB:0≤σ): ∃ T:ℝ,0 ≤ T∧∀ (c:Side)(x:Axis)(p:BudgetPoint)(A:St c)(η S:ℝ)(G:Silo c)(L:BankP c)(δ:ℝ), Run.Pack id id η δ B A S G L → Torch G→2*(σ+3)≤δ→ B ≤ p.B → p.power ≤ b→p.order ≤ n→p.threshold ≤η→ r*p.threshold < η/2→η ≤ 1 → 0 ≤ S ∧ Deposits (fun V=> Lat.shift 0 V x*A V - A V*Lat.shift 0 V x) p σ (T*S) (T*S*(p.threshold/η)) :=by
    obtain ⟨C,hc,H⟩:= magnet n b B hK; obtain ⟨K,hx,hy⟩:=applause B b n; let W:=payment 1 (4*B+2) 0 1 1 (C*K*2) σ 0; refine ⟨W, ?_,fun c x p A η S G L δ hp h hr hb ht hQ hP hX hD=>?_⟩
    · unfold W payment degreeIncome; have hp:0≤1-Real.exp (-1):= sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)); positivity
    let T:=EraM c; let f(i:T):= strip x i.val; let Z(i:T): ParcelZ (c:=c):=⟨i.val.1,i.val.2.1+step x,f i,newDay x i.val G⟩; let Ξ(i:T):= C*basePrice L x i.val* tribute B b n (strip x i.val); let Y(i:T):= Ξ i*(p.threshold/η); have hu:=p.threshold_pos.trans_le hP
    have he(i:T): (Z i).Ticket p (Ξ i) (Y i) B:=by
       obtain ⟨⟨he,hh,hM,-,-,hN,hg⟩,hu'⟩:= H c x A η δ S G L hp h p ht hQ hP hX hD i.val i.2; obtain ⟨ha,hX,Hx,hf⟩:=primeM x i.val i.2; exact ⟨ha,hf,mul_nonneg he (by unfold tribute; positivity), hh,hM,hg,(fun n U=> hN U n),fun a V=>colorV G x V hp hu hD i a,flatClaws G _ _ hu hp h,(hu' i.val.1 ha).1,fun o hi=> (fun V hv l hl hh=> (hu' o hi).2 V hv l hl hh)⟩
    have hE:= budget_nonneg (footA x hp 0 0); refine ⟨by linarith,?_⟩ -- refine Deposits order
    have hF: Ac.Hit f p.B Ξ σ (W*S):=by
        have hh : Ac.Hit f B Ξ σ (W*S):=by
            refine Eq.mp (congr_arg (Ac.Hit f B Ξ σ) ?_) (candle G x C hp hc b n hB hr K (zero_le_one.trans hx) (hy _)); unfold W payment degreeIncome; ring
        intro z; apply budget_mono (hh z) (fun i=>ite_nonneg (mul_nonneg (he i).tk (Real.exp_pos _).le) le_rfl) fun i=>?_; split; next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (YM.Next.Scheduling.cover_earns hb _)) hB)) (he i).tk
        next h=> exact le_rfl
    have hY: Ac.Hit f p.B Y σ (W*S*(p.threshold/η)):=by
        let M:= p.threshold/η; have hm:0 ≤ M:= div_nonneg p.threshold_pos.le hu.le; intro x; convert budget_scale hm (hF x) using 1
        · funext i; split <;> rename_i hj; unfold Y; unfold M; ring
          rw [mul_zero]
        exact mul_comm ..
    refine ⟨T,inferInstance,Z,⟨Ξ,Y,fun _=>B,he,hF,hY⟩,funext fun i=>?_⟩; rw [← sumEra G x hp hu]; exact (Finset.sum_apply i univ (fun j:T=> (Z j).val)).symm
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.prepaid
