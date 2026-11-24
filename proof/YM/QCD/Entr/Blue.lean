import YM.QCD.Entr.Tower
/-! # xferm projection tape. Gives actual evaluates WITHOUT scalars; β reset then operates. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
variable {ι β:Type}(G:Gem c N ι)(F:Gem c N β)(b:Flavor N)
variable [Fintype β] (h:SlotT F p a σ P U)(he: Licence p σ t a G)(ht:0<a)(hz:0≤σ)
noncomputable def widthμ (σ:ℝ)(N:ℕ):=Real.exp σ*9*fingers N^2*‖goldW‖
lemma μworth :0≤widthμ σ N:=by unfold widthμ; positivity
include h
lemma reading_off (V:Grid c)(d θ:ℝ):
    let E:=elog F d θ; HasSum (fun i=> (offT E p.threshold).mean i V) (((-θ) • paleF N (U V)+(-d) • paleF N (1:Sheet c))-Patron.total E p.threshold V):=by
    intro E; unfold Patron.total; rw [tsum_fintype]; let P':= paleF N (1: Sheet c); rw [show (((-θ):ℝ) • paleF N (U V)+(-d) • P')=(∑ i,E.view i V) from ?_,← sum_sub_distrib];
    · exact hasSum_fintype _
    rw [Fintype.sum_sum_type]; change _=((∑ i,(-θ) • F.view i V)+(∑ i,(-d) • (pointQ N c).view i V)); rw [← Finset.smul_sum, ← Finset.smul_sum, h.trunk,stemSum]
include ht hz
lemma crediting (x θ:ℝ)(hw:u+1+1≤σ)(hv:0≤u) :
    let E:=elog F x θ;let d':= (|θ| *P+|x| *widthμ σ N) *a^2
    Crossing E ∧ AnchorT E p a σ d' ∧ Purchases (offT E p.threshold) p.threshold p.B u (payment 1 (4*p.B+2) 0 1 1 d' u 0) a :=by
    intro E v
    have hp: Crossing E:=pilot _ _ (clock _ _ h.moveG) (clock _ _ (passQ ..)); have hh:AnchorT E p a σ v:=by
       have hH:= formH _ _ (sizeζ F (-θ) h.warp) (sizeζ _ (-x) (stemQ (c:=c) N (q:=σ) p ht)); unfold v widthμ; rw [add_mul,show |θ| = |-θ| from (abs_neg _).symm, show |x|=|-x| from (abs_neg _).symm] -- simplifies weird
       convert! hH using 1; ring
    exact ⟨hp,hh, starsX E hh hp ht hv hw⟩
omit h ht hz
lemma shooting (N:ℕ) (P:ℝ)(hP:1≤P):∃ L:ℝ,1 ≤ L∧∀ (c:Side)(ι β :Type)[Fintype β],∀ (G:Gem c N ι)(F:Gem c N β)(p:BudgetPoint)(U:St c)(η σ t:ℝ),0 < η→0≤σ→SlotT F p η σ P U → Licence p σ t η G→∀ b:Flavor N,
    η^2*|legϑ G F b| ≤ L*t ∧ η^2*|legA G F b| ≤ L*t:=by
    obtain ⟨K,hK,H⟩:= hauteur N; have hp:=zero_le_one.trans hP; have hk:=zero_le_one.trans hK; let L:= K+2*K*(1+K*P); refine ⟨L,by unfold L; exact hK.trans (le_add_of_nonneg_right (by positivity)),fun c I J hF G F p U η σ t hv hh hQ hG b=>?_⟩
    obtain ⟨h1,h2⟩:= H _ _ _ _ _ _ _ hG hv hh b; obtain ⟨h3,h4⟩:=H _ _ _ _ _ _ _ hQ.warp.law hv hh b
    obtain ⟨_,hC,_⟩:= hG.zone; have ht:= budget_nonneg (hC 0)
    let T:=qWave (till F b 0)
    have hj:1/2≤ T:=hQ.earn b; have hJ:0<T:=by linarith
    have h5 : η^2*|legϑ G F b| ≤ 2*K*t:=by unfold legϑ; rw [abs_div, abs_of_nonneg hJ.le,←mul_div_assoc]; refine (div_le_iff₀ hJ).2 ?_; apply h2.trans; linarith only [mul_le_mul_of_nonneg_left hj (mul_nonneg hk ht)]
    have he : |qMass (till F b 0)|≤K*P:=by apply le_of_mul_le_mul_left (le_trans h3 ?_) (sq_pos_of_pos hv); exact le_of_eq (by ring)
    refine ⟨h5.trans (mul_le_mul_of_nonneg_right (by unfold L; nlinarith only [show 0≤K*(K*P) by positivity,hk]) ht),?_⟩
    apply (mul_le_mul_of_nonneg_left (abs_sub _ _) (show 0≤η^2 from (sq_nonneg _))).trans -- need abs_sub_le
    rw [mul_add,abs_mul,← mul_assoc (η^2)]; apply (add_le_add h1 (mul_le_mul h5 he (abs_nonneg _) (by positivity))).trans; unfold L; nlinarith
include h ht hz he
lemma settles (hP : Crossing G)(hw:u+1+1≤σ)(hx:0≤u):
    let θ:=legϑ G F b; let d:=legA G F b; let Q:=fiscal G F d θ; let S:=offT (elog F d θ) p.threshold
    let D:= (|θ| * P+|d| * widthμ σ N)*a^2
    qMass (till Q b 0)=0∧qWave (till Q b 0)=0∧ Crossing Q ∧ Licence p σ (t+D) a Q ∧ Purchases S p.threshold p.B u (payment 1 (4*p.B+2) 0 1 1 D u 0) a∧∀ V, HasSum (fun i=> S.mean i V) (Patron.total G p.threshold V-((nozzle c N (θ • U V+d • (1: Sheet c)))+Patron.total Q p.threshold V)):=by
    intro θ d Q S D; let E:=elog F d θ
    have he':= absolved G F b h he ht hz; obtain ⟨hg,hY,hS⟩:= crediting F h ht hz d θ hw hx
    refine ⟨he'.2,he'.1,pilot G E hP hg,guardL G E he hY.law,hS,fun i=>?_⟩
    have hy: Patron.total Q p.threshold i=Patron.total G p.threshold i+Patron.total E p.threshold i:=woven_sum G E _ (permits G he ht hz _) (permits E hY.law ht hz _); rw [hy]; rw [show nozzle c N _=θ • paleF N (U i)+d • paleF N (1:Sheet c) from ?_]
    have hR:= reading_off F h i d θ
    dsimp only [] at hR ⊢; simp only [neg_smul] at hR; abel_nf at hR ⊢; exact hR
    let A:= (nozzle c N).restrictScalars ℝ
    exact (map_add A _ _).trans (congr_arg₂ (·+·) (A.map_smul ..) (A.map_smul ..))
end YM.QCD.Entr
