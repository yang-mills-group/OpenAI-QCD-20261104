import YM.QCD.High.Coins
import YM.QCD.High.Wares
/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
-- Scale/add proof. Weaken conditional for E heads. exact HASpanic.
variable {ι' μ:Type}
open Finch Calm Stem Push.BetaTransport Ring0 Jets.Touch Collection WilsonStartup
variable (b:Flavor N){G:Gem c N ι} {Y:Ruby.Hue c N β}{K:PathData su}{O:Clip}{W: St c}
local notation "rK" => (1/8 : ℝ)
local notation "ZK" => Real.exp rK
abbrev Feat (f:Grid c→EvenA c N)(p:BudgetPoint)(b:Flavor N)(a r v u:ℝ):Prop:=∃ (I J:Type)(_: Countable I)(_:Countable J)(X:Gem c N I)(Y:Ruby.Hue c N J), Cameo X Y p b a r v u f
lemma foster {x y: Grid c→ EvenA c N}(h:Feat x p b a t u w)(hp:Feat y p b a t r P)(hx:0≤t)(hv:0<a) : Feat (x+y) p b a t (u+r) (w+P):=by
   obtain ⟨I₁,J,hI,hJ,X,Y,h⟩:= h; obtain ⟨I',J',hI',hJ',V,K,hp⟩:=hp; exact ⟨_,_,inferInstance,inferInstance,_,_,cones X Y b V K h hp hx hv⟩
lemma juice {x:Grid c→EvenA c N}(h:Feat x p b a t u w)(η:ℝ)(he:0 ≤ t)(ha:0<a) : Feat (η • x) p b a t (|η| *u) (|η| *w):=by
     obtain ⟨_,_,hI,hJ,V,K,h⟩:=h; exact ⟨_,_,hI,hJ,_,_,chase V K b _ h he ha⟩
lemma louder {x:Grid c→EvenA c N} (h:Feat x p b a t u w)(he:u ≤r)(hp:w≤P): Feat x p b a t r P:=by
    obtain ⟨_,_,hI,hJ,V,K,h⟩:=h; exact ⟨_,_,hI,hJ,_,_,{h with waveP:=scoreH _ h.waveP he,tax:=hikes _ h.tax hp}⟩
noncomputable def shrugs (B:ℕ) (c:Side):ℝ:=Φ B (-(13/8:ℝ)) c
lemma speedδ (P:BudgetPoint) (e:ℝ)(h:e<13/8) (H Z:ℝ): Tendsto (fun c:Side=> shrugs P.B c * (↑(Fintype.card (Site c))*(Φ P.B e c*H)+Z)) atTop (𝓝 0)∧Tendsto (fun c:Side=> shrugs P.B c*(Φ P.B e c*H+Z)) atTop (𝓝 0):=by
    have h0 :Tendsto (shrugs P.B) atTop (𝓝 0):=by change Tendsto (fun c=> shrugs P.B c) _ _; simpa only [pow_zero,mul_one,shrugs] using shine P.B (show 0<(13:ℝ)/8 from by norm_num) 0 1 zero_le_one -- unq
    let f (n:ℕ)(c: Side):= (Φ P.B (-(13/8-e)) c*(c.val:ℝ)^n)*H+shrugs P.B c*Z
    have h1(n): Tendsto (f n) atTop (𝓝 0):=by
        have hh:= shine P.B (sub_pos.mpr h) n 1 zero_le_one; simp only [mul_one] at hh; simpa only [zero_mul,zero_add] using (hh.mul_const H|>.add (h0.mul_const Z))
    have he c : Φ P.B (-(13/8-e)) c=shrugs P.B c*Φ P.B e c:=by unfold Φ shrugs; rw [←Real.exp_add]; congr 1; ring -- Φ nested
    constructor
    · exact (h1 4).congr (fun c=> by unfold f; rw [he,site_card]; push_cast; ring)
    exact (h1 0).congr (fun c=>by unfold f; rw [pow_zero,he]; ring)
variable (O:Clip)(K:PathData su)(hp:K.Bounds O σ A P) (he:Decent O p)(hV:2 ≤ p.B) (hw:Geo.Width p O σ)
lemma rootsH {X:Grid c→EvenA c N}(a:ℝ)(h:Feat X p b a r t w)(hp:0≤ r)(hz:0<a) (s:ℝ)(hu: |s| ≤ shrugs p.B c) : Feat (s • X) p b a r (shrugs p.B c*(max 0 t)) (shrugs p.B c *max 0 w):=by
   have hh:=Real.exp_pos ((-(13/8:ℝ)) * tollV p.B c); apply louder b (juice b h s hp hz) -- order
   · exact (mul_le_mul_of_nonneg_left (le_max_right ..) (abs_nonneg s)).trans (mul_le_mul_of_nonneg_right hu (le_max_left ..))
   exact (mul_le_mul_of_nonneg_left (le_max_right ..) (abs_nonneg s)).trans (mul_le_mul_of_nonneg_right hu (le_max_left ..))
-- fixed height/wep.W. universal shrinking cost after.Curr
lemma brisk (f :Side→ℝ)(h:Tendsto (fun c=> shrugs p.B c*f c) atTop (𝓝 0))(hc:0 < t):∀ᶠ c:Side in atTop, shrugs p.B c*max 0 (f c)≤ t:=by
   filter_upwards [h.eventually_le_const hc] with c h; cases le_total (f c) 0 with
   | inl z=> rw [max_eq_left z,mul_zero]; exact hc.le
   | inr z=> rw [max_eq_right z]; exact h
include hp he hw hV
abbrev back (x y z:ℝ)(K:PathData su)(O:Clip)(P:BudgetPoint)(W:St c)(N:ℕ): Grid c→EvenA c N:= x • topsK K O P c N+(y • (paleF N ∘ W)+z • (paleF N ∘ (1:St c)))
set_option maxHeartbeats 800000 in
lemma tonicP (a w v u ε:ℝ)(hz:0<a)(hx:a≤ w)(hu:0<u)(hv:0<ε)(hr:p.supportExponent=2):∀ᶠ c:Side in atTop,∀ (U:St c), (∃ X:Gem c N (LayerQ c),SlotT X p w (Quotes.preExponent p) v U) →∀ x y z:ℝ, |x|≤ shrugs p.B c→|y| ≤ shrugs p.B c→|z| ≤ shrugs p.B c→ Feat (back x y z K O p U N) p b a (rK+rK+1) u ε:=by
    let V:=rK+rK+1; have hK:V ≤ p.supportExponent:=by rw [hr]; unfold V; norm_num
    have hκ:0 < V:=by unfold V; positivity
    have hF: V <13/8:=by unfold V; norm_num
    let g:= price p V; let B₁:=regularNeed su p O σ A 0 (p.threshold^2); let D:=softNeed su p O σ A 0 (p.threshold^2); let F:=v*w^2; let K':=widthμ V N*a^2
    let d:=u/4; let t:=ε/4; have h_d:0<d:=by unfold d; positivity
    have h_t:0<t:=by unfold t; positivity
    filter_upwards [continueS.eventually_gt_atTop 20,brisk _ (speedδ p V hF g D).1 h_t,brisk _ (speedδ p V hF g B₁).2 h_d,brisk _ (speedδ p V hF F 0).1 h_t,brisk _ (speedδ p V hF F 0).2 h_d,brisk _ (speedδ p V hF K' 0).1 h_t,brisk _ (speedδ p V hF K' 0).2 h_d] with c hc h0 h1 h2 h3 h4 h5 U X x y z hx' hy hz'
    simp only [add_zero] at h2 h3 h4 h5
    obtain ⟨X,H⟩:=X; let W₁:= air X p.B; let L:= pointQ N c; have hh: 2 ≤ c.val:=by omega
    have hy: Feat (y • (paleF N ∘ U)) p b a V d t:=louder b (rootsH b a ⟨_,_,inferInstance,inferInstance,W₁,reef W₁ p.threshold false,liamG b (Calm.Shard.bloated _ H.warp (by unfold Quotes.preExponent; linarith)) H.moveG hκ hh hz hx H.trunk⟩ hκ.le hz y hy) h3 h2
    have ht : Feat (z • (paleF N ∘ (1:St c))) p b a V d t:=by
        have hp:= liamG (G:=L) b (stemQ N p hz) (passQ ..) hκ hh hz le_rfl (W:= (1:St c)) (fun i=>stemSum i N)
        exact louder b (rootsH b a ⟨_,_,inferInstance,inferInstance,_,_,hp⟩ hκ.le hz z hz') h5 h4
    -- hg huge inputs
    let T:= air (treeH N c) p.B; have hp₀:= mastH b hp he hw hc hz hκ.le hK hV; let R:=bedT K p c; let Y:=vowT K p O c; let M:= weave (linen T (-1)) (ostinato R Y N); let Q:=Ruby.HJoin (tint (reef T p.threshold true) (-1)) (riff R Y N)
    have hp':Feat (x • topsK K O p c N) p b a V d t:=louder b (rootsH b a ⟨_,_,inferInstance,inferInstance,M,Q,hp₀⟩ hκ.le hz x hx') h1 h0
    exact louder b (foster b hp' (foster b hy ht hκ.le hz) hκ.le hz) (by unfold d; linarith only [hu]) (by unfold t; linarith only [hv])
end YM.QCD.High
