import YM.QCD.Kites.Returns
import YM.QCD.Fall.Bake
/-! # output theorem as schematic mask-free turn of TRUE hats. basis & expense actual. -/
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







lemma accomplishmentsR (N R n:ℕ)(P:ℝ)(hP:1≤P):∃ l m:ℝ,1 ≤ l ∧ 1 ≤ m∧∀ (L:Side)(M u:ℝ),0<M→0<u →∀ᶠ x in atTop,∀ (c:Side)(p:BudgetPoint),20<c.val→p.power≤ R→ p.order ≤ n→p.B=radiusB x→u+1+1≤p.supportExponent+1 →∀ (X:St c)(P':PathData su)(v:Clip)(α η C Λ:ℝ),P'.Bounds v η C Λ→Decent v p→Geo.Width p v η→∀ (ι β ν μ:Type)[Countable ι][Countable β][Countable ν][Fintype μ] (b:Flavor N) (G:Gem c N ι)(F:Rail c N β)(H:Gem c N μ)(Y:Ruby.Hue c N ν)(t h a r A:ℝ),
    Crossing G → MixedP F → F.Reg p.threshold → (∀ V:Grid c,Summable (Ruby.tK F p.threshold V)) → SlotT H p h (Quotes.preExponent p) P X → Licence p (Quotes.preExponent p) t h G →0<a→1≤h→ 2*a ≤ h → l*t ≤ h^2*(1/2) → billH m l P t N p v η C α ≤ r → bankH m l P t N p v η C α+A ≤ pra L x → Purchases Y p.threshold p.B (p.supportExponent+1) A h → Quits F p.B 1 (priceK L M x) (u+1) h →
    let Z:=readyE G H b v P' p α; let T:= readyK G F Y H b v P' p α; let S:= powerU G H b; let B:= betaP G H b
    0<S∧S≤2∧ h^2*|legA G H b| ≤ l*t ∧ h^2*|legϑ G H b|≤ l*t ∧ p.threshold^2*|B| ≤ drains m l P t N p ∧ Photo p b Z T a r 1 (taxK L x 3) u ∧∀ V:Grid c,∀ (β τ:ℝ)(j:Grid c→ℝ),
       wearK c N S (scoreX G F Y p.threshold (fun U=> j U+(pulse P' v p β τ U-α*receipt P' v p U)) X V) = scoreV Z T p.threshold (fun U=> j U + pulse P' v p (β+α+B) (vac (stock (charm G H b)) τ) U) (X+mCoeff G H b • 1) V:=by
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
    refine ⟨hS',hj,hS,hq',hd, ⟨gustE _ hH _,hF',hx,hf,hd',hₓ,hm',fun i=>⟨permits _ hₓ h' hσ.le _,(story X₁ i _ _ (hM i)).summable⟩,zero_lt_one⟩,fun U β τ j=> ?_⟩
    let A i:=j i + pulse P' v p (β+α+B) (vac (stock (charm G W b)) τ) i
    let B'(i:Grid c):= j i+(pulse P' v p β τ i-α*receipt P' v p i); refine stationed G F Y X B' A (legϑ G W b) (legA G W b) hs.life hs Y' h1 hz' hV ?_ hZ hH' (zero_lt_one.trans_le hV) hσ.le S hm U
    intro V; have hf:= hV' V β τ
    let K:=stock (charm G W b)
    unfold B' A; simp only [map_add] at *; unfold Y' B
    -- clarify typ
    abel_nf at hf ⊢; exact hf
end YM.QCD.Kites
