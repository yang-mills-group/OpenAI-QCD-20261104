import YM.QCD.Fall.Wait
import YM.Massive.Lantern.Light
/-! # stronger resonance. The normalized shift packages an explicit certificate of re-use at ANY K family with exact summability. The exponent recipe can stay fixed while K-label values on a marker disk are recomputed; need to merge separately with that family. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε S:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{X:St c}{ι β ν α ι':Type}
variable (G: Gem c N ι)(F: Rail c N β)(Y: Ruby.Hue c N ν) (W:Gem c N α)(Y': Ruby.Hue c N ι')
variable (b:Flavor N)


open WilsonStartup Collection Averaging Pressure Jets.Touch
variable {o:Rudder.Gleam} [Countable ι][Countable β][Countable ν][Fintype α]







lemma invokedAl (N R n:ℕ)(P:ℝ)(hP:1≤P):∃ l m:ℝ,1 ≤ l ∧ 1 ≤ m∧∀ (L:Side)(M u:ℝ),0<M→0<u →∀ᶠ x in atTop,∀ (c:Side)(p:BudgetPoint),20<c.val→p.power≤ R→ p.order ≤ n→p.B=radiusB x→u+1+1≤p.supportExponent+1 →∀ (X:St c)(P':PathData su)(v:Clip)(α η C Λ:ℝ),P'.Bounds v η C Λ→Decent v p→Geo.Width p v η→∀ (ι β ν μ:Type)[Countable ι][Countable β][Countable ν][Fintype μ] (b:Flavor N) (G:Gem c N ι)(F:Rail c N β)(H:Gem c N μ)(Y:Ruby.Hue c N ν)(t h a r A:ℝ),
    Crossing G → MixedP F → F.Reg p.threshold → (∀ V:Grid c,Summable (Ruby.tK F p.threshold V)) → SlotT H p h (Quotes.preExponent p) P X → Licence p (Quotes.preExponent p) t h G →0<a→1≤h→ 2*a ≤ h → l*t ≤ h^2*(1/2) → billH m l P t N p v η C α ≤ r → bankH m l P t N p v η C α+A ≤ pra L x → Purchases Y p.threshold p.B (p.supportExponent+1) A h → Quits F p.B 1 (priceK L M x) (u+1) h →
    let Z:=readyE G H b v P' p α; let T:= readyK G F Y H b v P' p α; let S:= powerU G H b; let B:= betaP G H b
    0<S∧S≤2∧ h^2*|legA G H b| ≤ l*t ∧ h^2*|legϑ G H b|≤ l*t ∧ p.threshold^2*|B| ≤ drains m l P t N p ∧ Photo p b Z T a r 1 (taxK L x 3) u ∧ Purchases (Ruby.HJoin Y (Entr.envy G H b P' v p α)) p.threshold p.B (u+1+1) (pra L x) h ∧ ∀ (I:Type)(R:Rail c N I), (∀ i,Summable (Ruby.tK R p.threshold i)) → ∀ V:Grid c,∀ (β τ:ℝ)(j:Grid c→ℝ),
       wearK c N S (scoreX G R Y p.threshold (fun U=> j U+(pulse P' v p β τ U-α*receipt P' v p U)) X V) = scoreV Z (readyK G R Y H b v P' p α) p.threshold (fun U=> j U + pulse P' v p (β+α+B) (vac (stock (charm G H b)) τ) U) (X+mCoeff G H b • 1) V:=by
    obtain ⟨l,m,hl,hm,H⟩:= Entr.kinetic N R n P hP; refine ⟨l,m,hl,hm,fun L M u hp he=>?_⟩; filter_upwards [bearKR L M u hp he.le, Work.E01.radiusB_tendsto.eventually_ge_atTop 2] with x hx hv
    intro c p h hP he' hB hu X P' v α η C Λ h0 h1 h2 ι β ν μ _ _ _ _ b G F W Y t k a r A hG hF hR hZ hk hq h' hV hE hL hT hU hs hz Z T S B
    let X':= Entr.tele G W b P' v p α; let Y':= Entr.envy G W b P' v p α
    obtain ⟨hq',hS,hA,hp',hH,hH',hd,hB',hV'⟩:= H c X p v P' Λ η C α he' hP (hB ▸ hv) h h0 h1 h2 ι μ G W t k b hV hG hq hk
    have hK : |legϑ G W b|≤ (1/2:ℝ):=le_of_mul_le_mul_left (hq'.trans hL) (by positivity : 0<k^2)
    let s:=1+legϑ G W b; have hp : 1/2≤ s:=by unfold s; linarith [abs_le.mp hK|>.1]
    have hξ:0<s:=by linarith
    have hS' :0<S:= inv_pos.mpr (Real.sqrt_pos.2 hξ)
    have hm : S^2*s=1:=by change (Real.sqrt s)⁻¹^2*_=_; rw [inv_pow,Real.sq_sqrt hξ.le,inv_mul_cancel₀ hξ.ne']
    have hj: S≤2:=by nlinarith
    have hi:S*a ≤ k:= (mul_le_mul_of_nonneg_right hj h'.le).trans hE
    let Y₁:=Ruby.HJoin Y Y'; let X₁:=Ruby.Trail Y₁ F p.threshold; let q:=p.supportExponent+1
    have hσ:p.supportExponent > 0 := p.exponent_pos; have hz': 0≤q:=by unfold q; linarith
    have h1: Purchases Y' p.threshold p.B q (bankH m l P t N p v η C α) k:=hB';
    have hh:= joinsM _ _ hs h1; have hm':Quits T p.B 1 (taxK L x 3) u a:= excess X₁ (hx c N _ _ Y₁ F p k hB hz (scant _ hh hu (by rw [add_comm]; exact hU))) h' hS' hi
    obtain ⟨hd',hF'⟩:= gustK X₁ (Ruby.wheel Y₁ F hh.projection hF p.threshold) (Ruby.plant Y₁ F hh.life hR) S -- argument order
    have hM :∀ U:Grid c,Summable (Ruby.tK X₁ p.threshold U):= by
       intro U; obtain ⟨he,hV⟩:=heart Y₁ hh hz' hV U; exact (Ruby.plenary Y₁ F U (hZ U) hh.life he hV).summable
    obtain ⟨hf,hx⟩:=pears X' S b hp' hA
    have hₓ:Licence p p.supportExponent r a Z:=irises X' (scoreH X' hH' hT) h'.le hS'.le hi
    refine ⟨hS',hj,hS,hq',hd, ⟨gustE _ hH _,hF',hx,hf,hd',hₓ,hm',fun i=>⟨permits _ hₓ h' hσ.le _,(story X₁ i _ _ (hM i)).summable⟩,zero_lt_one⟩, scant _ hh hu (by rw [add_comm]; exact hU),fun I F hzK U β τ j=> ?_⟩
    let A i:=j i + pulse P' v p (β+α+B) (vac (stock (charm G W b)) τ) i
    let B'(i:Grid c):= j i+(pulse P' v p β τ i-α*receipt P' v p i); refine stationed G F Y X B' A (legϑ G W b) (legA G W b) hs.life hs Y' h1 hz' hV ?_ hzK hH' (zero_lt_one.trans_le hV) hσ.le S hm U
    intro V; have hf:= hV' V β τ
    let K:=stock (charm G W b)
    unfold B' A; simp only [map_add] at *; unfold Y' B
    -- clarify typ
    abel_nf at hf ⊢; exact hf
end YM.QCD.Kites

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
lemma arrivalR (j N:ℕ)(S:RG.Stage)(Q:Plan j)(u θ:ℝ)(ht:0<θ)(hz:0<u)(hh:u+1+1≤ S.supportExponent+1)(hC:S.clip.direct≤1):∃ K U V':ℝ,0<K∧0<U∧1 ≤ V'∧∀ (a r G W:ℝ),0<a→0<r→∃ M:ℕ, ∀ (L:Side)(μ v:ℝ),0<μ→0<v→ ∀ᶠ x in atTop, let e:= K*chip L x; let t:= betaF su x L; let β:= fan L θ x; let l:=2*β
   ∀ (c:Side)(p:BudgetPoint)(P:PathData su) (X: Offer 1 a G)(Y:Offer 2 r W)(D:Train j) (C:ℝ), M≤ c.val→Now L p S x→P.Bounds S.clip S.width S.paths C→let Z:= wood Q 0 D+blossomT X Y (haloK L x) c
   ∃ F:Gem c N (LayerQ c), SlotT F p l (Quotes.preExponent p) V' Z ∧∀ α:ℝ,|α| ≤ v →∀ (ι ι' ν:Type)[Countable ι][Countable ι'][Countable ν],∀ (H:Gem c N ι)(R:Rail c N ι')(J:Ruby.Hue c N ν)(b:Flavor N), Crossing H → Licence p (S.supportExponent+3) e l H → MixedP R → R.Reg p.threshold → (∀ V, Summable (Ruby.tK R p.threshold V)) → Quits R p.B 1 (priceK L μ t) (u+1) l → Purchases J p.threshold p.B (p.supportExponent+1) (overA L x θ) l →
      let l':=legϑ H F b; let s:=powerU H F b; let V:=betaP H F b; let T₁:=readyE H F b S.clip P p α; let T₂:=readyK H R J F b S.clip P p α
      0<s∧s≤2∧ |V| ≤1 ∧ l^2*|legA H F b| ≤ U*e∧l^2*|l'| ≤ U*e ∧ Photo p b T₁ T₂ β (chip L x) 1 (taxK L x 3) u ∧ Purchases (Ruby.HJoin J (Entr.envy H F b P S.clip p α)) p.threshold p.B (u+1+1) (pra L t) l ∧∀ (I:Type)(G:Rail c N I),(∀ i,Summable (Ruby.tK G p.threshold i)) → ∀ (U' : Grid c)(B τ:ℝ)(j:Grid c→ℝ), wearK c N s (scoreX H G J p.threshold (fun U=> j U+(pulse P S.clip p B τ U-α*receipt P S.clip p U)) Z U') = scoreV T₁ (readyK H G J F b S.clip P p α) p.threshold (fun U=>j U+pulse P S.clip p (B+α+V) (vac (Reggae.stock (charm H F b)) τ) U) (Z+mCoeff H F b • 1) U':=by
    let σ:= S.supportExponent+3; have hS :0≤ σ:=by unfold σ; have h:= S.price_pos; positivity
    obtain ⟨P,hP,H⟩:=basis_paid j Q S.power S.order N σ hS; obtain ⟨l,m,hl,hm,hu⟩:=invokedAl N S.power S.order P hP; obtain ⟨K,hK,hI⟩:=saleBudget S hC N l m P hl hm hP
    refine ⟨K,l,P,hK,by linarith,hP,fun a r G W he ha=> ?_⟩; obtain ⟨t,η,B,n,h,hB,hQ⟩:= H a r G W he ha; refine ⟨max n 21,fun L μ v hM hv=>?_⟩
    filter_upwards [(Work.E09.betaF_growth su L).eventually (hu L μ u hM hz),hI L v hv B,birthed L t η h hB,framesC L θ ht] with x hg hh' hx hY e w β k c p Q' X Y D C hN hZ hA Z
    obtain ⟨ha',hΘ,hL,hS⟩:= hh' p hZ; obtain ⟨F,hV⟩:= hQ X Y D c ((le_max_left ..).trans hN) _ hx.1 hx.2.1; obtain ⟨h1,h2,h3⟩:= hZ.era; have h' :0<β:=fan_pos ..; have hj:1≤k:=by unfold k; have h2:1≤β:=hY.2.1; linarith
    have hv : SlotT F p k (Quotes.preExponent p) P Z:=by rw [Quotes.preExponent,h3]; exact hV k (by linarith) p h1.le h2.le ha' (hZ.baseG ▸ hx.2.2)
    refine ⟨F,hv,?_⟩; intro α ha ι ι' ν eJ eV eW T R S' b hC' he' hF' hp hs hy hG θ0 s W' U₁ U₂; rw [show S.supportExponent+3= Quotes.preExponent p from by rw [← h3];rfl] at he'
    have hn: 20 < c.val:= lt_of_lt_of_le (show 20 < 21 by omega) ((le_max_right ..).trans hN)
    obtain ⟨ha₁,ha₂,ha₃,ha₄⟩:= hS α ha
    obtain ⟨hQ,h₁,h₂,h₃,h₄,h₅,hμT,h₆⟩:= hg c p hn h1.le h2.le hZ.ball (h3.symm ▸ hh) Z Q' S.clip α S.width S.paths C hA hΘ hL ι ι' ν (LayerQ c) b T R F S' e k β (chip L x) (overA L x θ) hC' hF' hp hs hv he' h' hj le_rfl (ha₁.trans (by nlinarith : 1/2 ≤ k^2*(1/2))) ha₃ (by unfold overA; linarith only [ha₂,hY.1]) hG hy
    refine ⟨hQ,h₁,le_of_mul_le_mul_left (h₄.trans (by rw [mul_one];exact ha₄)) (pow_pos p.threshold_pos 2),h₂,h₃,Tide U₁ U₂ _ h₅ ?_ ?_ ,hμT,h₆⟩
    · exact (Real.exp_pos _).le
    apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (by norm_num); have hp:=Real.exp_le_exp.mp (show _≤ _ from hY.2.2.1); simpa only [one_mul] using hp
end YM.QCD.Kites

#print axioms YM.QCD.Kites.arrivalR
