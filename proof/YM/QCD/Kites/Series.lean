import YM.QCD.Kites.Clock
/-! # sustainability under published estimates, including PortD Jump slope expenditure. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{X:St c}{ι β ν α ι':Type}
open WilsonStartup Collection Averaging Pressure Jets.Touch Time ConnectedActivityE6
variable (S: RG.Stage)
variable (G: Gem c N ι)(F: Rail c N β)(Y: Ruby.Hue c N ν) (W:Gem c N α)(Y': Ruby.Hue c N ι')
variable (b:Flavor N)  
lemma tide (h:Quits F p.B w η a r)(hv:0≤t)(hz:t≤η): Quits F p.B w t a r:=by
    obtain ⟨f,hf,h⟩:=h.cost; have hT i :0≤ f i:=(norm_nonneg _).trans (h i 1); refine ⟨f,fun x=>?_,h⟩; refine budget_mono (hf x) ?_ ?_
    · intro i; split; exact mul_nonneg (mul_nonneg (pow_nonneg hv _) (hT _)) (Real.exp_pos _).le; exact le_rfl
    intro i; split; next h=> exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv hz _) (hT i)) (Real.exp_pos _).le
    next h=> exact le_rfl
lemma Tide (h:Photo p b G F a r u η q)(hv:0≤t)(hz:t≤η): Photo p b G F a r u t q:= { h with quoteK:= tide F h.quoteK hv hz }
variable [Countable ι][Countable β]
lemma further (L:Side)(p:BudgetPoint)(t:ℝ) (x:ℝ)(hv:0≤t)(hz:t ≤p.supportExponent)(hb:p.B=highR L x)(h:Photo p b G F (fan L η x) (chip L x) u (taxK L x 1) t): let W:= duo G F; Pant c N p.threshold W∧ W.Wave p.threshold∧ ∃ f g,Cents W f g (fan L η x) p.threshold∧ Fill W f g t t (taxK L x 1) 1 (chip L x) (highR L x):=by
   intro W'; obtain ⟨f,hf,hϕ⟩:= h.quoteE.zone; obtain ⟨g,hg,hQ⟩:= h.quoteK.cost; have he :0≤g:=fun i=>(norm_nonneg _).trans (hQ i 1); let θ:=fan L η x
   have hL:0<θ:=fan_pos ..; refine ⟨painted G F h.passE h.passK p.threshold,regimen _ _ (Licence_g h.quoteE) h.perm,f,g,⟨fun i=>(hϕ i).travel,he,?_,hQ⟩,hv,(Real.exp_pos _).le, ?_,?_⟩
   · intro i U; change Creek.load _ (light _ (masked p.threshold (G.addr i).support _ U))≤_; by_cases ht:Healthy p.threshold (G.addr i).support U
     · rw [masked_eq _ _ _ _ ht]; exact (shot (lens (G.addr i).site) _ θ hL).trans ((hϕ i).sizeU U ht)
     rw [masked_ne _ _ _ _ ht,map_zero,load_zero]; exact (hϕ i).travel
   · rw [← hb]; intro i; refine budget_mono (hf i) ?_ ?_
     · intro j; split <;> first| exact mul_nonneg (hϕ j).travel (Real.exp_pos _).le| exact le_rfl
     intro j; by_cases hv:(G.addr j).site=i
     · change ite ((G.addr j).site=i) _ _ ≤ _; rw [if_pos hv,if_pos hv]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _))) (hϕ _).travel
     exact (if_neg (show ¬ (W'.row j).site=i from hv)).le.trans ((hf i).1 _)
   rw [← hb]; rw [show (fun i => _)=GasP.taxed (Ruby.oriD F) g (taxK L x 1) from ?_]; · exact hg
   funext i; exact mul_comm ..
def overA (L:Side)(x θ:ℝ):ℝ:=pra L (betaF su x L)/2
-- not largest but sufficiently large
lemma horizons (j N:ℕ)(S:RG.Stage)(Q:Plan j)(u θ:ℝ)(ht:0<θ)(hz:0<u)(hh:u+1+1≤ S.supportExponent+1)(hC:S.clip.direct≤1):∃ K U:ℝ,0<K∧0<U∧∀ (a r G W:ℝ),0<a→0<r→∃ M:ℕ, ∀ (L:Side)(μ v:ℝ),0<μ→0<v→ ∀ᶠ x in atTop, let e:= K*chip L x; let t:= betaF su x L; let β:= fan L θ x; let l:=2*β
   ∀ (c:Side)(p:BudgetPoint)(P:PathData su) (X: Offer 1 a G)(Y:Offer 2 r W)(D:Train j) (C:ℝ), M≤ c.val→Now L p S x→P.Bounds S.clip S.width S.paths C→let Z:= wood Q 0 D+blossomT X Y (haloK L x) c
   ∃ F:Gem c N (LayerQ c), ∀ α:ℝ,|α| ≤ v →∀ (ι ι' ν:Type)[Countable ι][Countable ι'][Countable ν],∀ (H:Gem c N ι)(R:Rail c N ι')(J:Ruby.Hue c N ν)(b:Flavor N), Crossing H → Licence p (S.supportExponent+3) e l H → MixedP R → R.Reg p.threshold → (∀ V, Summable (Ruby.tK R p.threshold V)) → Quits R p.B 1 (priceK L μ t) (u+1) l → Purchases J p.threshold p.B (p.supportExponent+1) (overA L x θ) l →
      let l':=legϑ H F b; let s:=powerU H F b; let V:=betaP H F b; let T₁:=readyE H F b S.clip P p α; let T₂:=readyK H R J F b S.clip P p α
      0<s∧s≤2∧ |V| ≤1 ∧ l^2*|legA H F b| ≤ U*e∧l^2*|l'| ≤ U*e ∧ Photo p b T₁ T₂ β (chip L x) 1 (taxK L x 1) u ∧ ∀ (U' : Grid c)(B τ:ℝ)(j:Grid c→ℝ), wearK c N s (scoreX H R J p.threshold (fun U=> j U+(pulse P S.clip p B τ U-α*receipt P S.clip p U)) Z U') = scoreV T₁ T₂ p.threshold (fun U=>j U+pulse P S.clip p (B+α+V) (vac (Reggae.stock (charm H F b)) τ) U) (Z+mCoeff H F b • 1) U':=by
    let σ:= S.supportExponent+3; have hS :0≤ σ:=by unfold σ; have h:= S.price_pos; positivity
    obtain ⟨P,hP,H⟩:=basis_paid j Q S.power S.order N σ hS; obtain ⟨l,m,hl,hm,hu⟩:=accomplishments N S.power S.order P hP; obtain ⟨K,hK,hI⟩:=saleBudget S hC N l m P hl hm hP
    refine ⟨K,l,hK,by linarith,fun a r G W he ha=> ?_⟩; obtain ⟨t,η,B,n,h,hB,hQ⟩:= H a r G W he ha; refine ⟨max n 21,fun L μ v hM hv=>?_⟩
    filter_upwards [(Work.E09.betaF_growth su L).eventually (hu L μ u hM hz),hI L v hv B,birthed L t η h hB,framesC L θ ht] with x hg hh' hx hY e w β k c p Q' X Y D C hN hZ hA Z
    obtain ⟨ha',hΘ,hL,hS⟩:= hh' p hZ; obtain ⟨F,hV⟩:= hQ X Y D c ((le_max_left ..).trans hN) _ hx.1 hx.2.1; obtain ⟨h1,h2,h3⟩:= hZ.era; have h' :0<β:=fan_pos ..; have hj:1≤k:=by unfold k; have h2:1≤β:=hY.2.1; linarith
    have hv : SlotT F p k (Quotes.preExponent p) P Z:=by rw [Quotes.preExponent,h3]; exact hV k (by linarith) p h1.le h2.le ha' (hZ.baseG ▸ hx.2.2)
    refine ⟨F,?_⟩; intro α ha ι ι' ν eJ eV eW T R S' b hC' he' hF' hp hs hy hG θ0 s W' U₁ U₂; rw [show S.supportExponent+3= Quotes.preExponent p from by rw [← h3];rfl] at he'
    have hn: 20 < c.val:= lt_of_lt_of_le (show 20 < 21 by omega) ((le_max_right ..).trans hN)
    obtain ⟨ha₁,ha₂,ha₃,ha₄⟩:= hS α ha
    obtain ⟨hQ,h₁,h₂,h₃,h₄,h₅,h₆⟩:= hg c p hn h1.le h2.le hZ.ball (h3.symm ▸ hh) Z Q' S.clip α S.width S.paths C hA hΘ hL ι ι' ν (LayerQ c) b T R F S' e k β (chip L x) (overA L x θ) hC' hF' hp hs hv he' h' hj le_rfl (ha₁.trans (by nlinarith : 1/2 ≤ k^2*(1/2))) ha₃ (by unfold overA; linarith only [ha₂,hY.1]) hG hy
    refine ⟨hQ,h₁,le_of_mul_le_mul_left (h₄.trans (by rw [mul_one];exact ha₄)) (pow_pos p.threshold_pos 2),h₂,h₃,Tide U₁ U₂ _ h₅ ?_ hY.2.2.1,h₆⟩
    exact (Real.exp_pos _).le
end YM.QCD.Kites
