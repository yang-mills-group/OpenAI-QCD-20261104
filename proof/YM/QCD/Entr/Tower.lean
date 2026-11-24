import YM.QCD.Entr.Wood
/-! # pressure_calibration at cone continuation. real solved stencil and aperture exact. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
variable {ι β:Type}(G:Gem c N ι)(F:Gem c N β)(b:Flavor N)
lemma basis_paid (j:ℕ)(Q:Plan j)(R n N:ℕ) (σ:ℝ)(hs:0≤σ):∃ C:ℝ,1≤C∧∀ a r G W:ℝ,0<a→0<r→∃ t η:ℝ,∃ B M:ℕ,0<t ∧0<η∧∀ X:Offer 1 a G,∀ Y: Offer 2 r W,∀ v: Train j,∀ c:Side,M≤ c.val→∀ x:ℝ,0<x→x≤t→∃ V:Gem c N (LayerQ c),∀ w:ℝ,0<w→∀ p:BudgetPoint,p.power≤ R→p.order≤ n→B≤p.B→p.threshold ≤η*x^2→ SlotT V p w σ C (wood Q 0 v+ blossomT X Y x c):=by
    obtain ⟨C,η,B,M,hC,hp,H⟩:= authorized j Q N R n σ hs; obtain ⟨S,hS,T⟩:=hauteur N; refine ⟨C+1,by linarith,fun a r G W h h' => ?_⟩
    obtain ⟨D,κ,E,hE,hD,hF⟩:=fruitGrant h h' hs R n N G W; have hz:0<S*D:=mul_pos (by linarith) (by linarith)
    let t:=min 1 ((1/4)/(S*D)); refine ⟨t,min η κ,max B E,M,lt_min zero_lt_one (div_pos (by norm_num) hz),lt_min hp hE, fun X Y v c hM x hv hx=>?_⟩
    have hX:= hx.trans (min_le_left 1 _); have hY:= hx.trans (min_le_right 1 _)
    obtain ⟨P,hM,hT,hf⟩:= H c hM v; obtain ⟨V,hV,hW,hG⟩:=hF X Y c x hv hX; refine ⟨weave P V,fun w hw p hP hQ hk hz'=>?_⟩
    have hu: x^2≤1:= (pow_le_pow_left₀ hv.le hX _).trans_eq (one_pow _); obtain ⟨ha,hh⟩:=hf p hQ hP ((le_max_left ..).trans hk) (hz'.trans ((mul_le_mul (min_le_left ..) hu (sq_nonneg _) hp.le).trans_eq (mul_one _))) w hw
    have hb:=hG p ((le_max_right ..).trans hk) hP hQ (hz'.trans (mul_le_mul_of_nonneg_right (min_le_right ..) (sq_nonneg _))) w hw
    have hh':S*D*x ≤ (1/4:ℝ):=(mul_comm ..).trans_le ((le_div_iff₀ hz).1 hY)
    refine ⟨boost _ (formH _ _ ha hb) ?_,pilot _ _ hM hV,fun U=> ?_, fun b=> ?_⟩
    · rw [add_mul]; apply add_le_add_right; apply mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    · rw [Fintype.sum_sum_type]; change (∑ i,P.view i U)+(∑ i,V.view i U)=_; rw [hT,hW]; exact (Port.oneC ..).symm
    have he:= (T c _ V p σ _ w hb.law hw hs b).2; have hp' : |qWave (till V b 0)| ≤ 1/4:=by apply le_of_mul_le_mul_left (le_of_le_of_eq he rfl|>.trans ?_) (sq_pos_of_pos hw); nlinarith [mul_le_mul_of_nonneg_left hh' (sq_nonneg w)]
    rw [tune_add _ _ b ha.law hb.law hw hs,←awake,map_add,awake,awake]; obtain ⟨hy,hy'⟩:=abs_le.mp hp'
    obtain ⟨h₁,h₂⟩:=abs_le.mp (hh b); linarith

noncomputable def legϑ :ℝ:=qWave (till G b 0)/qWave (till F b 0)
noncomputable def legA :ℝ:= qMass (till G b 0)-legϑ G F b*qMass (till F b 0)
-- correction AGAINST SlotT. F must be placed last no Mask churn before output. ids. `preExponent`. exact.
noncomputable def elog (d f:ℝ): Gem c N (β ⊕ Site c):= weave (linen F (-f)) (linen (pointQ N c) (-d))
noncomputable def fiscal (d f:ℝ): Gem c N (ι⊕(β⊕Site c)):= weave G (elog F d f)
variable [Fintype β] (h:SlotT F p a σ P U)(he: Licence p σ t a G)(ht:0<a)(hz:0≤σ)
local notation "θ0"=> legϑ G F b
local notation "m0"=>legA G F b
include he h ht hz
lemma absolved : qWave (till (fiscal G F (m0) (θ0)) b 0)=0 ∧ qMass (till (fiscal G F (m0) (θ0)) b 0)=0:=by
    let θ:= θ0; let m:=m0; let Q:= elog F m θ; let E:=pointQ N c
    let k:= till F b 0; let T:=till G b 0; let j:=till E b 0; have hV:= h.warp; have hh:=stemQ (c:=c) N (q:=σ) p ht
    have hX : till (fiscal G F (m0) (θ0)) b 0=T+((-θ) • k+ (-m) • j):=(tune_add G Q b he (guardL _ _ (sizeζ F _ hV).law (sizeζ _ _ hh).law) ht hz).trans (by unfold Q elog; rw [tune_add _ _ b (sizeζ _ _ hV).law (sizeζ _ _ hh).law ht hz,tillζ,tillζ]) -- check placeholder
    rw [hX,← awake]; change _ ∧ bandQ (T+((-θ) • k+ (-m) • j))=0; simp only [map_add, map_smul,awake]; have hg : qWave k≠0:= by linarith [show _≤ qWave k from h.earn b]
    obtain ⟨hj,hj'⟩:=choices b (c:=c); change qWave T+((-θ)*qWave k+(-m)*qWave j)=0∧ qMass T +((-θ) *qMass k + (-m)*qMass j)=0; change qWave j=0 at hj'; change qMass j=1 at hj; rw [hj',hj]; unfold m; unfold legA; change qWave T+((-θ)*qWave k+ -legA G F b*0)=0 ∧ qMass T+((-θ)*qMass k+ -(qMass T - θ*qMass k)*1)=0 -- definition mismatch after unfolding m
    constructor; · rw [mul_zero,add_zero,neg_mul]; change qWave T+ - (qWave T/qWave k*qWave k)=0; rw [div_mul_cancel₀ _ hg,add_neg_cancel]
    ring
end YM.QCD.Entr
