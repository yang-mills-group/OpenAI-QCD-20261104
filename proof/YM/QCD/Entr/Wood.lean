import YM.QCD.Entr.Base
/-! # continued wood calibration. Splitting before post L increases. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
variable {ι β:Type}(G:Gem c N ι)(F:Gem c N β)(b:Flavor N)
lemma authorized (j:ℕ) (Q:Plan j) (N R n:ℕ)(σ:ℝ)(hs: 0≤σ): ∃ C η:ℝ, ∃ B M :ℕ,1 ≤ C∧0<η∧∀ c:Side, M ≤ c.val→∀ (v:Train j),∃ G: Gem c N (Tick c), Crossing G ∧ (∀ U, (∑ i,G.view i U)=paleF N (wood Q 0 v U))∧∀ p:BudgetPoint,p.order≤n→p.power≤ R→p.B ≥ B→p.threshold ≤ η→∀ a:ℝ,0<a → AnchorT G p a σ (C*a^2)∧∀ b: Flavor N,|qWave (till G b 0)-1| ≤1/4:=by
    let k:=σ+1; obtain ⟨B,η,K,hE,hK,H⟩:= banner Q k (by unfold k; linarith)
    obtain ⟨M,hM⟩:= wager Q B K; obtain ⟨C,hc,HZ⟩:= floating B R n N; let D:=max 1 (C*K); refine ⟨D,η,B,M,le_max_left .., hE,fun c hP v=>?_⟩; obtain ⟨Γ,Y,h,hh⟩:=candor (H c v)
    let G:=sealG Γ N; refine ⟨G,glossy h hh N,fun U=>setsK h U N,fun p hx h' hg hl a ht=> ?_⟩; have he:=HZ _ _ _ _ _ a _ _ h p hx h' hl hg ht σ hs le_rfl
    refine ⟨boost _ he ?_,fun b=>hM v c hP Y Γ η k N hE (by unfold k;linarith) h hh (Licence_g he.law) b p hg⟩
    rw [mul_right_comm C]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _)
lemma torchZ (X:Offer k a P)(hp:0<η)(ht:η ≤1)(hr:0<a) (H: Own c w t B (wild (frosting X.W) η c) q):∃ Γ Y, Run.Pack id id w t B (wild (frosting X.W) η c) q Γ Y ∧ Torch Γ :=by
    let p:=singleR c; let S:= wild (frosting X.W) η c
    have ht':Tow p (sun p) (sun p) S:= ⟨fun s g T U hh=> by have hx:=precious X η hp ht hr (raise p s) T g hh U; exact hx⟩
    have hx : (fun U=> foldH (S U))=S:=by funext i; let Q:= S i; change chirality c*star Q*chirality c=_; exact (by nth_rw 2 [← chi_star (n:=c)]; exact ((solidly X.W X.price hp ht hr (n:=c)).lane i).symm ) -- rw may both Q
                                            -- edit
    obtain ⟨Γ,Y,hB⟩:= H; obtain ⟨Γ,Y,H,L⟩:= honors hB ht'; exact carry H L hx
abbrev Panel (c:Side):=Tick c ⊕ Tick c
abbrev LayerQ (c:Side):=Tick c⊕Panel c
lemma fruitGrant (h:0 < a)(ht:0<r)(hs:0≤u)(b k N :ℕ) (P K:ℝ): ∃ C δ:ℝ,∃ B:ℕ,0<δ∧1≤C∧∀ X:Offer 1 a P,∀ V:Offer 2 r K,∀ c:Side,∀ s:ℝ, 0<s→ s≤1→ ∃ G:Gem c N (Panel c), Crossing G ∧ (∀ U, (∑ i,G.view i U)=paleF N (blossomT X V s c U))∧∀ p:BudgetPoint,B ≤ p.B → p.power ≤ b→ p.order ≤ k→ p.threshold ≤ δ*s^2→∀ w:ℝ,0<w→ AnchorT G p w u (C*s*w^2) :=by
    obtain ⟨t',D,M,he,hD,H⟩:= richP 1 h (show 0≤u+1 from by linarith)
    obtain ⟨v,W,n,hF,hW,I⟩:=richP 2 ht (show 0≤u+1 from by linarith)
    let B:=max M n; obtain ⟨C,hC,H'⟩:=floating B b k N; let Z:=D*|P|+W*|K|; let δ:=min t' v; let A:=1+C*Z; have hc:0≤Z:=by unfold Z; positivity
    have hp:1≤A:=le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hC) hc); refine ⟨A,δ,B,lt_min he hF,hp,fun X V c s hS ht' =>?_⟩
    obtain ⟨Γ,Y,hB,hT⟩:= torchZ X hS ht' h (H _ _ _ X.price _ hS ht' c B (le_max_left ..)); obtain ⟨Z',Y',hB',hT'⟩:= torchZ V hS ht' ht (I _ _ _ V.price _ hS ht' c B (le_max_right ..))
    let G:= sealG Γ N; let F:= sealG Z' N; refine ⟨weave G F, pilot G F (glossy hB hT N) (glossy hB' hT' N),fun U=> ?_,fun p hi hj hq hz w h'=>?_⟩
    · rw [Fintype.sum_sum_type]; change (∑ i,(sealG Γ N).view i U)+(∑ i,(sealG Z' N).view i U)=_; rw [setsK hB,setsK hB']; exact (Port.oneC ..).symm
    have hh:= H' _ _ _ _ _ w _ _ hB p hq hj (hz.trans (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _))) hi h' u hs le_rfl; have hm:= H' _ _ _ _ _ w _ _ hB' p hq hj (hz.trans (mul_le_mul_of_nonneg_right (min_le_right ..) (sq_nonneg _))) hi h' u hs le_rfl
    apply boost (weave G F) (formH G F hh hm); rw [← mul_add,pow_one]; apply (mul_le_mul_of_nonneg_left (show _ ≤ D*|P| *s+W*|K| *s from ?_) (show 0≤C*w^2 from by positivity)).trans; rotate_left -- issue b
    · apply add_le_add ?_ ?_
      · gcongr; exact le_abs_self _
      apply le_trans (b:=W*|K| *s^2) ?_ ?_; · gcongr; exact le_abs_self _
      apply mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    unfold A Z; nlinarith [sq_nonneg w,mul_nonneg hS.le (sq_nonneg w)] -- abel
structure SlotT {ι:Type} [Fintype ι] (G:Gem c N ι)(p:BudgetPoint)(η σ C :ℝ)(F:St c):Prop where
 warp : AnchorT G p η σ (C*η^2)
 moveG : Crossing G
 trunk (V:Grid c): (∑ i,G.view i V)= paleF N (F V)
 earn (b:Flavor N): 1/2 ≤ qWave (till G b 0)
-- predictor price.C pre C' post. bazaar.
end YM.QCD.Entr
