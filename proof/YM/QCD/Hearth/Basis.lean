import YM.QCD.Hearth.Oral
import YM.QCD.Hearth.Grit
import YM.QCD.Hearth.Heat
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
open Hearth Pressure ConnectedActivityE6
variable {T H:ℝ→ℝ}
lemma coatσ (L:Side)(w:ℝ):∀ᶠ x in atTop,∀ (c:Side),vizR (run L x)≤ c.val→ flash (radiusB (run L x)) c*w ≤ shrugs (radiusB (run L x)) c:=by
   filter_upwards [wonderful (Rate.const (G:=su) (L:=L) w) (1/8) 1 0 (by norm_num) zero_lt_one] with x hx c hc; let B:= radiusB (run L x); have he:= hx c hc; simp only [pow_zero,mul_one] at he
   let g:=Φ B (-(1/8:ℝ)) c; have ht:g*w≤1:=(mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le).trans (show g*|w|≤1 from he)
   change flash B c*w ≤ shrugs B c; apply le_trans _ (mul_le_of_le_one_right (Real.exp_pos _).le ht); rw [show flash B c=shrugs B c*g from ?_,mul_assoc]; exact le_rfl
   unfold flash shrugs g Φ; rw [←Real.exp_add]; congr 1; ring
lemma flashκ (L:Side)(A:ℝ)(hp:Rate su L a (fun x=> (T x)⁻¹)):∀ᶠ x in atTop,∀ (c:Side),vizR (run L x)≤ c.val →0<T x →flash (radiusB (run L x)) c*A < T x:=by
   have hk:= hp.mul_left A; filter_upwards [wonderful hk (7/4) (1/2) 0 (by norm_num) (by norm_num)] with x hx c hc ht; let B:=radiusB (run L x); have hh : flash B c*|A*(T x)⁻¹| ≤1/2:=by unfold flash; rw [show (-7/4:ℝ)=-(7/4:ℝ) from by ring]; simpa only [pow_zero,mul_one] using! hx c hc
   apply (div_lt_one ht).mp; have hv:= (mul_le_mul_of_nonneg_left (le_abs_self (A*(T x)⁻¹)) (show 0≤flash B c from (Real.exp_pos _).le)).trans hh; rw [div_eq_mul_inv,mul_assoc]; exact hv.trans_lt (by norm_num)
lemma crownσ (c:Side)(B N:ℕ)(hx:Φ B (-(7/4:ℝ)) c* (c.val:ℝ)^4 * (8*(24*N):ℝ) ≤1/8) :∀ v:ℝ,0 ≤ v→ |v^2-1| ≤ flash B c*8→ Steep c N v:=by
    intro v hv hP
    let z:= flash B c; have hp:v≤ 1+ z*8:= by
        by_cases h:v≤1; · exact h.trans (by have hZ:0< z:=Real.exp_pos _; linarith only [hZ])
        have he:1 ≤ v:=le_of_not_ge h|>.trans (le_refl _); linarith only [le_self_pow₀ he (show 2 ≠0 by omega), (abs_le.mp hP).2]
    -- note graph notation problems
    let x:=Fintype.card (Keys c N);
    apply le_trans (show _≤ (Real.exp (z*8))^x from pow_le_pow_left₀ (hv.trans (le_max_right ..)) (max_le (Real.one_le_exp (mul_nonneg (Real.exp_pos _).le (by positivity))) (hp.trans ((add_comm ..).trans_le (Real.add_one_le_exp _)))) x); rw [← Real.exp_nat_mul]; apply Real.exp_monotone; rw [show (x:ℝ)= (c.val:ℝ)^4*(24*N) from dime ..]; rw [show Φ B (-(7 / 4:ℝ)) c=z from by unfold z flash Φ; ring_nf] at hx; linarith only [hx]
variable (K:PathData su)(O:Clip)(χ:PlaqAxes)(hp:K.Bounds O σ A P)(he: Decent O p)(hw:Geo.Width p O σ)(h0: p.supportExponent=2)(hV:2 ≤ p.B)
variable (ht:0 < Jets.Touch.chip L y)(hA:0<ε)(hT:1 ≤ fan L η y)(hR:p.B=highR L y)(hM:∀ c:Side,SkyH p L y η c N)
omit K O
variable {G':Stage} {Λ:ℝ}
local notation "rK" => (1/8:ℝ)
lemma coverE (Z:Stage)(Q:ℝ) {Φ':ℝ→ℝ} (hp:Rate su L u (fun x=> (Φ' x)⁻¹))(h0:Z.supportExponent=2) (η:ℝ)(hv:0<η):∀ᶠ y in atTop,∀ p:BudgetPoint,Now L p Z y→2 ≤ p.B→ 1 ≤ fan L η y→0< Jets.Touch.chip L y→∀ (K:PathData su) (A W:ℝ), K.Bounds Z.clip Z.width Z.paths A → Decent Z.clip p → Geo.Width p Z.clip Z.width → 0<Φ' y→ ∀ (c:Side), SkyH p L y η c N → vizR (run L y)≤ c.val →∃ φ μ Y, KeysG c p K Z.clip L y η Q W b χ (Φ' y) φ μ Y:=by
   let v:= Jets.Touch.chip L; let f:= fan L η; let B:= speedP L η
   have ht:Rate su L 0 f:= Rate.rpow_monitor η; have hB':Rate su L 0 B:= ht.mul_left 2; have hk:Rate su L 0 (fun x=> (f x)⁻¹):= (skin_i L η).ruled; have hu:Rate su L 0 (fun x=>(B x)⁻¹):= (hk.mul_left 2⁻¹).congr (Eventually.of_forall (fun i=> by unfold B speedP; unfold f; simp [mul_comm]))
   let d y:=v y-Real.exp (-1)*v y; have hy:Rate su L 1 (fun x=>(d x)⁻¹):=(top_chip L|>.mul_right (1-Real.exp (-1))⁻¹).congr (Eventually.of_forall fun x=>by dsimp only; rw [show d x=(1-Real.exp (-1))*v x from (by unfold d; ring)]; simp [v,mul_comm])
   have hF:=tonicR b Z d (fun _=>1) f B _ _ _ _ Q hy hB' ht (by simpa only [inv_one] using Rate.const (G:=su) (L:=L) (1:ℝ)) h0 -- metav
   obtain ⟨p',hL⟩:= Project.organK b (θ:=2+3) (by norm_num) hu hB' Q
   filter_upwards [liftsK χ L Z h0, raysR χ (Jets.Touch.chip_rate L) N,hF, Project.passB b true hk (Jets.Touch.chip_rate L),Project.passB b false hk (Jets.Touch.chip_rate L),hL, coatσ L 8,coatσ L (8*p'+4), flashκ L (20+8*p') hp,wonderful (Rate.const (L:=L) (G:=su) (8*(24*N):ℝ)) (7/4) (1/8) 4 (by norm_num) (by norm_num),wonderful (Rate.const (L:=L) (G:=su) 1) (7/4) (1/64) 0 (by norm_num) (by norm_num)] with y h1 h2 h10 h3 h4 h5 h7 h8 h6 h9 h₀ p he hv hT ht K A W hp' hD hK hc c hM hk
   let t:=f y; let g:=v y; have hA:= he.ball; have hx:0 < t:= fan_pos ..; have hB:t ≤B y:= le_mul_of_one_le_left hx.le (by norm_num : (1:ℝ)≤2); have he':0 <B y:=hx.trans_le hB
   have hd:0<d y:= sub_pos.mpr (mul_lt_of_lt_one_left ht (Real.exp_lt_one_iff.mpr (by norm_num)))
   let O:=Z.clip; obtain ⟨φ,M,u,hφ,h1⟩:= h1 _ _ K t _ hx hp' hD hK he hk -- argument order c p A u V!
   obtain ⟨u',δ,h2⟩:=h2 c p t hx he.baseG hA hk; obtain ⟨p₁,hH⟩:=height simple χ p c; let z:=min p₁ (min u u'); let v:=|W| * |M|
   have h₅: Quotes.preExponent p=2+3:=by rw [Quotes.preExponent,he.era.2.2,h0]
   have h7:=h7 c hk; rw [← hA] at h7; have h8:=h8 c hk; rw [← hA] at h8; have h6:=h6 c hk hc; rw [← hA] at h6; have h9:= h9 c hk; rw [← hA,abs_of_nonneg (show 0≤ (8:ℝ)*(24*N) from (by positivity))] at h9
   have hKc :flash p.B c≤1/64:= by have hp := h₀ c hk; rw [← hA,abs_one,pow_zero,mul_one,mul_one] at hp; unfold flash; rw [show (-7/4:ℝ)=-(7/4:ℝ) from (by ring)]; exact hp
   have hf:0<φ:=by linarith
   refine ⟨φ,z,v+δ,hf,fun G U HV HG p₀ m T hm hp=>?_⟩
   obtain ⟨X,hU⟩:= HV
   let κ:=flash p.B c; let μJ (j:Bool):=unitF j c (meter b (Patron.total G.P p.threshold 1)); obtain h:= HG.portraitP; have hr0 : Licence p 2 g t G.P:= he.era.2.2.trans h0 ▸ h.quoteE -- direction
   obtain ⟨e₁,hG,h2⟩:= h2 _ G.P h.passE h.pure2 hr0; obtain ⟨hrg,hx₁⟩:= h5 c p hA he' hk (LayerQ c) X U (h₅ ▸ hU)
   obtain ⟨s,Q₀,hQs,hQ,hL,hN,hC,hX,hY⟩:=tuneH hrg hx₁ (h3 c p hx hA hk _ G.P hr0 h.passE h.pure1) (h4 c p hx hA hk _ G.P hr0 h.passE h.pure1) hKc hm
   let α:=e₁/φ; have hξ: |α| ≤ κ*2:=by unfold α; rw [abs_div, abs_of_pos hf]; apply (div_le_iff₀ hf).mpr; apply hG.trans; change κ≤ _; linarith only [mul_le_mul_of_nonneg_left hφ (show 0 ≤κ from (Real.exp_pos _).le)]
   change κ*8 ≤ _ at h7; change κ≤ _ at hKc
   have hv':Feat (back α (s^2-1) (s^2*m-Q₀) K O p U N) p b t (rK+rK+1) (d y) 1:=h10 p he hx hB hd zero_lt_one K _ hp' hD hv hK c hk U ⟨X,hU⟩ α _ _ (hξ.trans ((by linarith only [hG,hξ,h7,abs_nonneg α] : _ ≤ shrugs p.B c))) (hC.trans h7) (hX.trans h8)
   obtain ⟨X₀,hX,hω⟩:= publishG b p G K U HG s α Q₀ p₀ m 0 hQs (he.era.2.2.trans h0) hA hM T (crownσ c _ _ h9 s hQs.le hC) hT hv' -- reduce.
   let V:=Finch.scent (c:=c) T p K O p₀ 0 N; let Y:=scoreV G.P G.K p.threshold V (U+m • 1); let A:= bio p X₀ K O U T (p₀+α) Q₀
   have he(i):wearK c N s (Y i)= A i:= hω i
   have hr(j :Bool): tollM j b (A 1)= s^2 * (unitF j c (U 1)+(if j then 0 else m)+μJ j):=by rw [←he, tollM, grassK,map_smul,show unitF j c (fumes b (Y 1))= _ from spoke b V G.P G.K p U m j]; rfl
   refine ⟨X₀,Q₀,s,α,hX,hY.trans_lt h6,hQs,hQ,by linarith only [hKc,hξ],hω,hrg,?_,?_,?_,?_,?_⟩ -- minor
   · intro i hi; change mud (A i)≠0; rw [← he,proofM]; unfold Y; rw [ζpt _ _ _ _ _ hi,Coda.term]; exact Complex.exp_ne_zero _
   · change tollM true b (A 1)=_; rw [hr true,if_pos rfl, add_zero]; exact hL
   · change tollM false b (A 1)=_; rw [hr false,if_neg (by decide)]; exact hN
   · rw [show Roll T p K O A= Roll _ _ _ _ Y from (funext (fun i=>by unfold Roll glaze; rw [← he,proofM]))]; rw [show (p₀+α)*φ=p₀*φ+e₁ from (by unfold α; field_simp)]; exact PrismT.scroll h1 h2 (show Lab0 su c p χ p₁ from hH) (le_trans (mul_le_mul_of_nonneg_left (le_abs_self M) (abs_nonneg p₀)) (mul_le_mul_of_nonneg_right (hp.trans (le_abs_self W)) (abs_nonneg M))) -- eff mul_le needs lower M. fix.
   refine ⟨lt_min hH.1 (lt_min h1.upT h2.upT),fun i hi=>hH.2 i ⟨hi.1,hi.2.trans (min_le_left ..)⟩⟩
end PrismT
end YM.QCD.High
#print axioms YM.QCD.High.PrismT.azure
