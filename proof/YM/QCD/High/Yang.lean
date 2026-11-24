import YM.QCD.High.Yin
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
namespace PrismT
open Acre Rails
open Stew.Project
variable {χ: PlaqAxes} {f:Grid c→EvenA c N}{κ:ℕ→Atom su 2}{L:Side}{y v α p₀ d₀:ℝ}
structure NormG (W:St c) (b:Flavor N) (f:Grid c→EvenA c N) (p:BudgetPoint) (F:PathData su) (O:Clip)(κ:ℕ→Atom su 2) (χ:PlaqAxes)(φ μ Y α m:ℝ):Prop where
    shade (U:Grid c): flags p.threshold U=∅ → mud (f U) ≠0
    lea : tollM true b (f 1)=unitF true c (W 1)
    life : tollM false b (f 1)=unitF false c (W 1)+m
    pulse : PulseS p χ su (Roll κ p F O f) (α*φ) Y μ
    run : Lab0 su c p χ μ -- ensure μ common.M.
lemma oasisP {O:Clip} (h:NormG W b f p K O κ χ t v z α u)(hx:0 <a) : NormG W b (a • f) p K O κ χ t v z α u:=by
     let Y:= Roll κ p K O f; let G i:= Y i-Real.log a; have he (j:Bool): tollM j b ((a • f) 1)=tollM j b (f 1):=congr_arg (unitF j c) (fogL b a _ hx)
     refine ⟨fun i hp=>?_ , (he true).trans h.lea, (he false).trans h.life, immigrate h.pulse h.pulse.upT le_rfl ?_,h.run⟩
     · change clay c N ((a:ℂ) • f i)≠0; rw [map_smul]; exact mul_ne_zero (by exact_mod_cast hx.ne') (h.shade i hp)
     intro w hw; rw [pulseAgree (A:=Roll _ _ K O (a • f)) (D:=G) p.threshold_le (show ∀ i,flags p.threshold i=∅ → Roll κ p K O (a • f) i=G i from fun i hi=>by
        unfold G Y Roll; rw [Pi.smul_apply,railM _ _ hx (h.shade i hi)]; ring) h.run hw] -- lem name
     have he i:sec i G w=sec i Y w:=by unfold G sec; ring
     unfold Ring0.glow Ring0.signal; dsimp only; simp_rw [he]; rfl
-- score forms
set_option quotPrecheck false
noncomputable abbrev bio (p:BudgetPoint)(V:Voice c N)(K:PathData su)(O:Clip)(U:St c)(κ:ℕ→Atom su 2)(α m:ℝ):Grid c→EvenA c N:=scoreV V.P V.K p.threshold (Finch.scent κ p K O α 0 N) (U+m • 1)
local notation "rK" => (1/8:ℝ)

abbrev SkyH (p:BudgetPoint)(L:Side)(y η:ℝ)(c:Side)(N:ℕ):Prop:=∀ (I V:Type)(Y:Ruby.Hue c N I)(X: Patron.Rail c N V), Quits X p.B 1 (taxK L y 3) (rK+rK) (fan L η y) → Purchases Y p.threshold p.B (rK+rK+1) 1 (fan L η y) → Quits (Ruby.Trail Y X p.threshold) p.B 1 (taxK L y 1) rK (fan L η y)
structure KeysG (c: Side)(p:BudgetPoint)(D:PathData su)(O:Clip)(L:Side)(x t H W:ℝ)(b:Flavor N)(k:PlaqAxes)(κ φ μ Y:ℝ):Prop where
   gift:0 <φ
   immigrates(G:Voice c N)(U:St c): (∃ X:Gem c N (LayerQ c),SlotT X p (speedP L t x) (Quotes.preExponent p) H U) → Glory L p b t x 1 G→∀ (p₀ m:ℝ)(T:ℕ→ Atom su 2),|m| ≤2 →|p₀|≤ W →∃ (A:Voice c N)(Z w α:ℝ), Enn p b L x t rK (duo A.P A.K)∧ |m-Z|<κ ∧0<w∧w≤2∧ |α|≤1∧ (∀ U',wearK c N w (bio p G D O U T p₀ m U')=bio p A D O U T (p₀+α) Z U') ∧ 1/4 ≤ unitF true c (U 1) ∧ NormG U b (bio p A D O U T (p₀+α) Z) p D O T k φ μ Y (p₀+α) Z
variable (K:PathData su)(O:Clip)(χ:PlaqAxes)(hp:K.Bounds O σ A P)(he: Decent O p)(hw:Geo.Width p O σ)(h0: p.supportExponent=2)(hV:2 ≤ p.B)
variable (ht:0 < Jets.Touch.chip L y)(hA:0<ε)(hT:1 ≤ fan L η y)(hR:p.B=highR L y)(hM:∀ c:Side,SkyH p L y η c N)
include hp he hw h0 hV ht hA hT hR hM
lemma azure (W Q: ℝ) :∀ᶠ c:Side in atTop,∃ φ μ Y,KeysG c p K O L y η Q W b χ ε φ μ Y:=by
   let x:= y; let t:=fan L η y; have hx:= fan_pos L η y; let g:=Jets.Touch.chip L y; let d:= g-Real.exp (-1)*g; have hd:0<d:= sub_pos.mpr (mul_lt_of_lt_one_left ht (Real.exp_lt_one_iff.mpr (by norm_num)))
   let B:=speedP L η x; have hB:t≤B:= (le_mul_of_one_le_left hx.le (by norm_num : (1:ℝ) ≤2)); have hψ:=tonicP b O K hp he hV hw t B Q d 1 hx hB hd zero_lt_one h0 -- order F
   have hu :1< Quotes.preExponent p:=by rw [Quotes.preExponent,h0]; linarith
   obtain ⟨p',hz⟩:= Project.orient b p hu (hx.trans_le hB) Q
   have hF:=flash_top p.B; have hF₁:= hF.mul_const (20+8*p'); rw [zero_mul] at hF₁
   filter_upwards [hF.eventually_le_const (by norm_num : (0:ℝ)<1/64), pureG χ K O p hp h0 he hw t hx, keeps χ p hx g N, chargeQ b true p g hx, chargeQ b false p g hx, hz, hF₁.eventually_lt_const hA, coatP p 8, coatP p (8*p'+4), crownT p.B N,hψ] with c hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
   obtain ⟨φ,M,u,hφ,h1⟩:= h1; obtain ⟨u',δ,h2⟩:=h2; obtain ⟨p₁,hH⟩:=height simple χ p c; let z:=min p₁ (min u u'); let v:=|W| * |M|
   have hf:0<φ:=by linarith
   refine ⟨φ,z,v+δ,hf,fun G U HV HG p₀ m T hm hp=>?_⟩
   obtain ⟨X,hU⟩:= HV
   let κ:=flash p.B c; let μJ (j:Bool):=unitF j c (meter b (Patron.total G.P p.threshold 1)); obtain h:= HG.portraitP; have hr0 : Licence p 2 g t G.P:= h0 ▸ h.quoteE -- direction
   obtain ⟨e₁,he,h2⟩:= h2 _ G.P h.passE h.pure2 hr0; obtain ⟨hrg,hx₁⟩:= h5 (LayerQ c) X U hU
   obtain ⟨s,Q₀,hQs,hQ,hL,hN,hC,hX,hY⟩:=tuneH hrg hx₁ (h3 _ G.P hr0 h.passE h.pure1) (h4 _ G.P hr0 h.passE h.pure1) hc hm
   let α:=e₁/φ; have hξ: |α| ≤ κ*2:=by unfold α; rw [abs_div, abs_of_pos hf]; apply (div_le_iff₀ hf).mpr; apply he.trans; change κ≤ _; linarith only [mul_le_mul_of_nonneg_left hφ (show 0 ≤κ from (Real.exp_pos _).le)]
   change κ*8 ≤ _ at h7; change κ≤ _ at hc
   have hv':Feat (back α (s^2-1) (s^2*m-Q₀) K O p U N) p b t (rK+rK+1) d 1:=h10 U ⟨X,hU⟩ α _ _ (hξ.trans ((by linarith only [he,hξ,h7,abs_nonneg α] : _ ≤ shrugs p.B c))) (hC.trans h7) (hX.trans h8)
   obtain ⟨X₀,hX,hω⟩:= publishG b p G K U HG s α Q₀ p₀ m 0 hQs h0 hR (hM c) T (h9 s hQs.le hC) hT hv' -- reduce.
   let V:=Finch.scent (c:=c) T p K O p₀ 0 N; let Y:=scoreV G.P G.K p.threshold V (U+m • 1); let A:= bio p X₀ K O U T (p₀+α) Q₀
   have he(i):wearK c N s (Y i)= A i:= hω i
   have hr(j :Bool): tollM j b (A 1)= s^2 * (unitF j c (U 1)+(if j then 0 else m)+μJ j):=by rw [←he, tollM, grassK,map_smul,show unitF j c (fumes b (Y 1))= _ from spoke b V G.P G.K p U m j]; rfl
   refine ⟨X₀,Q₀,s,α,hX,hY.trans_lt h6,hQs,hQ,by linarith only [hc,hξ],hω,hrg,?_,?_,?_,?_,?_⟩ -- minor
   · intro i hi; change mud (A i)≠0; rw [← he,proofM]; unfold Y; rw [ζpt _ _ _ _ _ hi,Coda.term]; exact Complex.exp_ne_zero _
   · change tollM true b (A 1)=_; rw [hr true,if_pos rfl, add_zero]; exact hL
   · change tollM false b (A 1)=_; rw [hr false,if_neg (by decide)]; exact hN
   · rw [show Roll T p K O A= Roll _ _ _ _ Y from (funext (fun i=>by unfold Roll glaze; rw [← he,proofM]))]; rw [show (p₀+α)*φ=p₀*φ+e₁ from (by unfold α; field_simp)]; exact PrismT.scroll h1 h2 (show Lab0 su c p χ p₁ from hH) (le_trans (mul_le_mul_of_nonneg_left (le_abs_self M) (abs_nonneg p₀)) (mul_le_mul_of_nonneg_right (hp.trans (le_abs_self W)) (abs_nonneg M))) -- eff mul_le needs lower M. fix.
   refine ⟨lt_min hH.1 (lt_min h1.upT h2.upT),fun i hi=>hH.2 i ⟨hi.1,hi.2.trans (min_le_left ..)⟩⟩
end PrismT
end YM.QCD.High
#print axioms YM.QCD.High.PrismT.azure
