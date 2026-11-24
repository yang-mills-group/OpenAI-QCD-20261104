import YM.QCD.Hearth.Focus
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
open Hearth Acre Pressure ConnectedActivityE6
variable {L:Side}{f g g₀:ℝ→ℝ}
local notation "V'"=> rK+rK+1
lemma dutch (h:Rate su L a f)(d:ℕ)(ε Z:ℝ)(hx: Z<13/8)(hp: Rate su L ε (fun x=> (g x)⁻¹)) :∀ᶠ x in atTop,∀ c:Side, 0<g x→ vizR (run L x)≤ c.val →
      shrugs (radiusB (run L x)) c * ((c.val:ℝ)^d*(Φ (radiusB (run L x)) Z c *|f x|)) ≤ g x / 2:=by
    filter_upwards [wonderful (h.mul hp) (13/8-Z) (1/2) d (by linarith) (by norm_num)] with x hx c hv hg
    have hh:= hx c hg; let B:=radiusB (run L x); change Φ B _ c*_ *_ ≤ _ at hh
    rw [abs_mul,abs_of_nonneg (inv_pos.mpr hv).le, show Φ B (-(13/8-Z)) c = shrugs B c*Φ B Z c from ?_] at hh
    · rw [show g x/2=(1/2)* g x by ring]; apply (div_le_iff₀ hv).mp; apply le_trans _ hh; exact le_of_eq (by change shrugs B c * ((c.val:ℝ)^d*(Φ B _ c *|f x|)) / g x= _; ring)
    unfold shrugs Φ; rw [← Real.exp_add]; ring_nf
lemma groveH (h:Rate su L a f)(hf:Rate su L t g)(hr:Rate su L r (fun x=> (g₀ x)⁻¹)) (hx: V'<13/8):∀ᶠ x in atTop,∀ c:Side,0<g₀ x → vizR (run L x)≤ c.val →let B:=radiusB (run L x); let X:=Φ B V' c*|f x|; let Y:= |g x|; shrugs B c * (↑(Fintype.card (Site c))*X + Y)≤g₀ x ∧ shrugs B c*(X+Y)≤g₀ x:=by
    filter_upwards [dutch h 4 r V' hx hr, dutch hf 0 r 0 (by norm_num) hr] with x hx hY c hp hc B X Y
    have hm:= hx c hp hc; have hv:= hY c hp hc; simp only [pow_zero,one_mul] at hv; have ht:shrugs B c*Y ≤ g₀ x/2:=by unfold Φ at hv; simpa only [zero_mul,Real.exp_zero,one_mul] using hv
    have he : shrugs B c*(↑(Fintype.card (Site c))*X) ≤g₀ x/2:=by rw [site_card]; push_cast; exact hm
    have hh : 0 ≤ X:=mul_nonneg (Real.exp_pos _).le (abs_nonneg _); have hχ:0 ≤ shrugs B c:= (Real.exp_pos _).le; have hJ: (1:ℝ) ≤ ↑(Fintype.card (Site c)):=by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance:Nonempty (Site c)) -- maybe >0 vs succ
    refine ⟨by rw [mul_add]; linarith only [he,ht],?_⟩; rw [mul_add]; linarith only [mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hh hJ) hχ,he,ht]
lemma spotK (G:Stage)(r:ℝ) (P:BudgetPoint)(h:Time.Same G P): price P r=P.threshold^2 * price (Time.probe G) r:=by
    unfold price bodyBill; rw [show pairBill su P=pairBill su (Time.probe G) from ?_]; rotate_left; · unfold pairBill Time.probe; simp only [h.1,h.2.1]
    simp_rw [show (Time.probe G).threshold=1 from rfl,one_pow,mul_one,← mul_assoc,←sum_mul]; ring
set_option maxHeartbeats 800000 in
lemma tonicR (S:Stage)(f g a w:ℝ→ℝ)(i j k d v:ℝ)(hp': Rate su L i (fun x=> (f x)⁻¹))(hw': Rate su L j w)(ha: Rate su L k a)(hK: Rate su L d (fun x => (g x)⁻¹)) (hs:S.supportExponent=2):∀ᶠ y in atTop,∀ p:BudgetPoint, Now L p S y→ 0<a y→ a y≤ w y→0<f y →0<g y→∀ (K:PathData su)(P:ℝ), K.Bounds S.clip S.width S.paths P→Decent S.clip p→ 2 ≤ p.B→ Geo.Width p S.clip S.width→∀ c:Side, vizR (run L y)≤ c.val →∀ (U:St c), (∃ X:Gem c N (LayerQ c),SlotT X p (w y) (Quotes.preExponent p) v U) →∀ x y' z:ℝ, |x|≤ shrugs p.B c→|y'| ≤ shrugs p.B c→|z| ≤ shrugs p.B c→ Feat (back x y' z K S.clip p U N) p b (a y) (rK+rK+1) (f y) (g y):=by
    let C:=V'; let G₁(x):=fiery su x L^2*price (Time.probe S) C; have hC:C <13/8:=by unfold C; norm_num
    let T (x):=f x/4; let U(x):=g x/4
    have h0:Rate su L i (fun x=> (T x)⁻¹):=(hp'.mul_left 4).congr (Eventually.of_forall (fun x=>by unfold T; simp [div_eq_mul_inv]))
    have h1:Rate su L d (fun x=> (U x)⁻¹):=(hK.mul_left 4).congr (Eventually.of_forall (fun x=>by unfold U; simp [div_eq_mul_inv]))
    let r:=Time.base su S; let q:=Time.softCeiling su S 1; let t(x):= r*fiery su x L^2; let m(x:ℝ):= q*(1+ ↑(radiusB (run L x)))^4 *fiery su x L
    have hg: Rate su L ((-(1/2))*2) G₁:=(Rate.flame.pow 2|>.mul_right (price (Time.probe S) C)); have hr:Rate su L ((-(1/2))*2) t:=(Rate.flame.pow 2|>.mul_left r);
    have hm:Rate su L (0+(-(1/2))) m:= (Rate.mul ((radH L).mul_left q) Rate.flame)
    have hF := (hw'.pow 2).mul_left v; have hY:=(ha.pow 2).mul_left (widthμ V' N)
    filter_upwards [groveH hg hr h0 hC, groveH hg hm h1 hC, groveH hF (Rate.const 0) h0 hC, groveH hF (Rate.const 0) h1 hC, groveH hY (Rate.const 0) h0 hC, groveH hY (Rate.const 0) h1 hC] with u h₁ h₂ h₃ h₄ h₅ h₆ p hK hz hx hu hv K P hp he hV hw c hk U' hU' x y z hx' hy hz'
    obtain ⟨X,H⟩:=hU'
    let O:=S.clip; have hc:20<c.val:= (seen _ c hk).2
    let u':=w u; let A:=a u; let V:=V'; have hk':V ≤p.supportExponent:=by unfold V; rw [hK.era.2.2,hs]; norm_num
    have h_d:0<T u:=div_pos hu (by positivity); have h_t:0<U u:= div_pos hv (by positivity); let t1:= (Fintype.card (Site c):ℝ)
    have hv:0 ≤ t1:= Nat.cast_nonneg _
    have hψ:0≤ shrugs p.B c :=(Real.exp_pos _).le; let F:= Φ p.B V' c; have hQ :0≤ F:=(Real.exp_pos _).le
    have ht : softNeed su p O S.width S.paths 0 (p.threshold^2) ≤ |m u|:=by
        have hh:= (Time.soft_table su S hK.era (show |(0:ℝ)|≤1 from (by norm_num)) (sq_nonneg p.threshold) le_rfl); simp only [hK.ball,hK.baseG] at hh
        rw [hK.baseG]; exact hh.trans (le_abs_self _)
    have ht': regularNeed su p O S.width S.paths 0 (p.threshold^2) ≤ |t u|:=by
        rw [Time.table su S hK.era]; simp only [abs_zero,zero_mul,mul_zero,add_zero,hK.baseG]; exact le_abs_self _
    have hg': price p V ≤ |G₁ u|:= by rw [spotK S V p hK.era, hK.baseG]; exact le_abs_self _
    have hT (r w A s:ℝ)(hA:0 ≤w)(hs:0≤ s)(hp:r ≤w)(ht:A≤ s)(hz:shrugs p.B c*(F*w+s) ≤T u):shrugs p.B c*max 0 (F*r+A) ≤T u:=by
         apply le_trans _ hz; apply mul_le_mul_of_nonneg_left _ hψ; exact max_le (add_nonneg (mul_nonneg hQ hA) hs) (add_le_add (mul_le_mul_of_nonneg_left hp hQ) ht)
    have hK'(r w A s:ℝ)(hA:0 ≤w)(hs:0≤ s)(hp:r ≤w)(ht:A≤ s)(hz:shrugs p.B c*(t1*(F*w)+s) ≤U u):shrugs p.B c*max 0 (t1*(F*r)+A) ≤U u:=by
         apply le_trans _ hz; apply mul_le_mul_of_nonneg_left _ hψ; exact max_le (add_nonneg (mul_nonneg hv (mul_nonneg hQ hA)) hs) (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hQ) hv) ht)
    let W₁:= air X p.B; let U0:= pointQ N c; have hh:2 ≤ c.val:=by omega
    have hκ:0<V:=by unfold V; norm_num
    have h7:=h₃ c h_d hk ; have h8:= h₄ c h_t hk; have h9:= h₅ c h_d hk; have h10:=h₆ c h_t hk; simp only [← hK.ball,abs_zero,add_zero] at h7 h8 h9 h10
    have hy : Feat (y • (paleF N ∘ U')) p b A V (T u) (U u):=by
        apply louder b (rootsH b A ⟨_,_,inferInstance,inferInstance,W₁,reef W₁ p.threshold false,liamG b (Calm.Shard.bloated _ H.warp (by unfold Quotes.preExponent; linarith only [hk'])) H.moveG hκ hh hz hx H.trunk⟩ hκ.le hz y hy)
        · have he' := hT (v*w u^2) _ 0 0 (abs_nonneg _) le_rfl (le_abs_self _) le_rfl (by simpa only [add_zero] using h7.2); simpa only [add_zero] using he'
        have he' := hK' (v*w u^2) _ 0 0 (abs_nonneg _) le_rfl (le_abs_self _) le_rfl (by simpa only [add_zero] using h8.1); simpa only [add_zero] using he'
    have ht'' : Feat (z • (paleF N ∘ (1:St c))) p b A V (T u) (U u):=by
        have hp:= liamG (G:=U0) b (stemQ N p hz) (passQ ..) hκ hh hz le_rfl (W:= (1:St c)) (fun i=>stemSum i N)
        apply louder b (rootsH b A ⟨_,_,inferInstance,inferInstance,_,_,hp⟩ hκ.le hz z hz')
        · have he' := hT (widthμ V' N*A^2) _ 0 0 (abs_nonneg _) le_rfl (le_abs_self _) le_rfl (by simpa only [add_zero] using h9.2); simpa only [add_zero,widthμ] using he'
        have he' := hK' (widthμ V' N*A^2) _ 0 0 (abs_nonneg _) le_rfl (le_abs_self _) le_rfl (by simpa only [add_zero] using h10.1); simpa only [add_zero,widthμ] using he'
    let T':= air (treeH N c) p.B; have hp₀:= mastH b hp he hw hc hz hκ.le hk' hV; let R:=bedT K p c; let Y:=vowT K p O c; let M:= weave (linen T' (-1)) (ostinato R Y N); let Q:=Ruby.HJoin (tint (reef T' p.threshold true) (-1)) (riff R Y N)
    have hp':Feat (x • topsK K O p c N) p b A V (T u) (U u):=by
        apply louder b (rootsH b A ⟨_,_,inferInstance,inferInstance,M,Q,hp₀⟩ hκ.le hz x hx')
        · have hp':= (h₁ c h_d hk).2; rw [← hK.ball] at hp'; exact hT _ _ _ _ (abs_nonneg _) (abs_nonneg _) hg' ht' hp'
        have hp':= (h₂ c h_t hk).1; rw [← hK.ball] at hp'; exact hK' _ _ _ _ (abs_nonneg _) (abs_nonneg _) hg' ht hp'
    exact louder b (foster b hp' (foster b hy ht'' hκ.le hz) hκ.le hz) (by unfold T; linarith only [hu]) (by unfold U; linarith only [‹0<g u›])
end YM.QCD.High
