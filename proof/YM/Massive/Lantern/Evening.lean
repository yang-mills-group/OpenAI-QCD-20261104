import YM.Massive.Lantern.Light
import YM.QCD.High.Yang
/-! Second merger resonance. -/
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
open Acre Acre.Rails
local notation "rK" => (1/8:ℝ)
variable {L:Side}{x C P' :ℝ}
def transferVoice (S:Voice c N) (s t:ℝ) {I J:Type} [Countable I][Countable J] (P: Gem c N I)(U: Ruby.Hue c N J): Voice c N:= letI := glazeP U (flightK S.K s); ⟨_,_,weave (flightE S.P s) P,Ruby.Trail U (flightK S.K s) t ⟩
structure Reliant (p:BudgetPoint)(S D:Voice c N)(K:PathData su)(O:Clip)(X:St c)(J:ℕ→ Atom su 2)(s α ν β₀ m v a:ℝ):Prop where
    steep : Steep c N s
    bears : ∃ (I J':Type)(_ : Countable I)(_:Countable J')(P:Gem c N I)(T:Ruby.Hue c N J'), let A:=transferVoice S s p.threshold P T; Purchases T p.threshold p.B (rK+rK+1) 1 a ∧ D=A∧∀ (Q:Type)(U: Patron.Rail c N Q),(∀ i,Summable (Ruby.tK U p.threshold i)) → ∀ (V:Grid c), wearK c N s (scoreV S.P U p.threshold (Finch.scent J p K O β₀ v N) (X+m • 1) V)= scoreV A.P (Ruby.Trail T (flightK U s) p.threshold) p.threshold (Finch.scent J p K O (β₀+α) v N) (X+ν • 1) V
variable (p:BudgetPoint)(S:Voice c N)(K:PathData su) (X:St c)
section indicated
variable {Q:Stage}(h:Glory L p b η x 1 S)(s α ν β₀ m v v':ℝ)(hv:0<s)(ht:p.supportExponent=2)(he:p.B=highR L x)
variable (hV:∀ (I V:Type)(Y:Ruby.Hue c N I)(X: Patron.Rail c N V), Quits X p.B 1 (taxK L x 3) (rK+rK) (fan L η x) → Purchases Y p.threshold p.B (rK+rK+1) 1 (fan L η x) → Quits (Ruby.Trail Y X p.threshold) p.B 1 (taxK L x 1) rK (fan L η x))
local notation "E!"=> Jets.Touch.chip L x
set_option quotPrecheck false
include hV h he hv ht
lemma pitcherG (J:ℕ→Atom su 2)(hz: Steep c N s)(hQ:1 ≤ fan L η x)(hy: Feat (back α (s^2-1) (s^2*m-ν) K O p X N) p b (fan L η x) (rK+rK+1) (E!-Real.exp (-1)*(E!)) 1):∃ A:Voice c N, Enn p b L x η rK (duo A.P A.K) ∧ Reliant p S A K O X J s α ν β₀ m v (fan L η x) ∧∀ (V: Grid c), wearK c N s (scoreV S.P S.K p.threshold (Finch.scent J p K O β₀ v N) (X+m • 1) V)= scoreV A.P A.K p.threshold (Finch.scent J p K O (β₀+α) v N) (X+ν • 1) V
:=by
   obtain ⟨I,Y,hI,hY,B,D,W⟩:=hy; let r:=fan L η x; let E:=flightE S.P s; let T:=flightK S.K s; let F:=weave E B; let H:=Ruby.Trail D T p.threshold; let Z:=h.portraitP; have hh:Countable (Ruby.Plot D T):=glazeP ..
   have hx:=fan_pos L η x; have hR:rK ≤ rK+rK+1:=by norm_num
   have hℓ:Licence p rK (Real.exp (-1)*(E!)) r E:=greys S.P hz (by rw [← ht]; exact Z.quoteE) hv hx
   have hh' :Licence p rK (E!) r F:=scoreH F (guardL E B hℓ (wells B W.waveP hR le_rfl)) (by linarith)
   have hk:= verses S.K hz (p:=p) Z.quoteK hv hx (Real.exp_pos _).le; have hy:Rise.Wave (duo S.P S.K) p.threshold:=regimen _ _ (Licence_g Z.quoteE) Z.perm
   obtain ⟨hX,hL⟩:=gustK S.K Z.passK Z.perm s; obtain ⟨hP,hT⟩:= pears _ _ b Z.pure2 Z.pure1
   have hα₁ :Wick F:=by intro i; cases i; exact fun hi=>⟨hP.face _,hP.van _ hi⟩; exact W.maskG _
   let A1: Voice c N:= transferVoice S s p.threshold B D
   have hPub (I:Type)(V: Patron.Rail c N I)(hF:∀ i,Summable (Ruby.tK V p.threshold i))(U:Grid c): wearK c N s (scoreV S.P V p.threshold (Finch.scent J p K O β₀ v N) (X+m • 1) U)= scoreV A1.P (Ruby.Trail D (flightK V s) p.threshold) p.threshold (Finch.scent J p K O (β₀+α) v N) (X+ν • 1) U:=by
    rw [eff S.P V U s p.threshold _ (X+m • 1) (hF U) (Z.boreal U).1 rfl]; refine routesC E (flightK V s) D U ?_ W.tax.life ((Kites.heart D W.tax (by norm_num) hQ U).2) (story V U s _ (hF U)).summable
    rw [heartS,heartS,show _root_.YM.QCD.Patron.total (A1.P) _ _=_ from (woven_sum E B U (t:=p.threshold) (sour S.P U s (Z.boreal U).1).summable (permits B W.waveP hx (by norm_num) U))]; apply Eq.mp (congr_arg (HasSum _) ?eq) (W.eyeG U)
    case eq=>
       have hp:= congr_fun (bdH p K α β₀ v J (O:=O) (c:=c) (N:=N)) U; dsimp only [comp_apply,Pi.sub_apply,Pi.smul_apply] at hp
       simp only [back, Pi.add_apply, Pi.smul_apply, Pi.one_apply,comp_apply]; -- simplifies topsK?
       let M:Sheet c→L[ℝ]EvenA c N:=(nozzle c N).restrictScalars ℝ; have hs : M (s^2 • (X U+m • 1))- M (X U+ν • 1)=(s^2-1) • paleF N (X U)+(s^2*m-ν) • paleF N (1:Sheet c):=by rw [← map_sub]; rw [show s^2 • (X U+m • 1)-(X U+ν • 1)=(s^2-1) • X U+(s^2*m-ν) • 1 from (by rw [smul_add,smul_smul,sub_smul, sub_smul,one_smul]; abel),map_add,map_smul,map_smul]; rfl
       change nozzle c N (s^2 • (X U+m • 1))- nozzle c N (X U+ν • 1)= _ at hs
       rw [← hp,← hs]; abel
   refine ⟨A1,levy b F H (pilot _ _ (gustE S.P Z.passE s) W.cover) (Ruby.wheel _ _ W.tax.projection hL _) hα₁ (fibs _ _ b hT W.atoms) (Ruby.plant D T W.tax.life hX) hh' (hV _ _ D T hk W.tax) he (by norm_num), ⟨hz,⟨I,Y,hI,hY,B,D,W.tax,rfl,hPub⟩⟩,?_⟩; exact hPub _ S.K (fun U=>(Z.boreal U).2)
end indicated
end YM.QCD.High
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
local notation "rK" => (1/8:ℝ)

structure EveningR (c: Side)(p:BudgetPoint)(D:PathData su)(O:Clip)(L:Side)(x t H W:ℝ)(b:Flavor N)(k:PlaqAxes)(κ φ μ Y ε:ℝ):Prop where
   gift:0 <φ
   immigrates(G:Voice c N)(U:St c): (∃ X:Gem c N (LayerQ c),SlotT X p (speedP L t x) (Quotes.preExponent p) H U) → Glory L p b t x 1 G→∀ (p₀ m:ℝ)(T:ℕ→ Atom su 2),|m| ≤2 →|p₀|≤ W →∃ (A:Voice c N)(Z w α:ℝ), Enn p b L x t rK (duo A.P A.K)∧ |m-Z|<κ ∧|w-1|≤ε ∧Reliant p G A D O U T w α Z p₀ m 0 (fan L t x) ∧0<w∧w≤2∧ |α|≤1∧ (∀ U',wearK c N w (bio p G D O U T p₀ m U')=bio p A D O U T (p₀+α) Z U') ∧ 1/4 ≤ unitF true c (U 1) ∧ NormG U b (bio p A D O U T (p₀+α) Z) p D O T k φ μ Y (p₀+α) Z
variable (K:PathData su)(O:Clip)(χ:PlaqAxes)(hp:K.Bounds O σ A P)(he: Decent O p)(hw:Geo.Width p O σ)(h0: p.supportExponent=2)(hV:2 ≤ p.B)
variable (ht:0 < Jets.Touch.chip L y)(hA:0<ε)(hT:1 ≤ fan L η y)(hR:p.B=highR L y)(hM:∀ c:Side,SkyH p L y η c N)
include hp he hw h0 hV ht hA hT hR hM
lemma evenings (W Q tol: ℝ) (hzT:0<tol) :∀ᶠ c:Side in atTop,∃ φ μ Y,EveningR c p K O L y η Q W b χ ε φ μ Y tol:=by
   let x:= y; let t:=fan L η y; have hx:= fan_pos L η y; let g:=Jets.Touch.chip L y; let d:= g-Real.exp (-1)*g; have hd:0<d:= sub_pos.mpr (mul_lt_of_lt_one_left ht (Real.exp_lt_one_iff.mpr (by norm_num)))
   let B:=speedP L η x; have hB:t≤B:= (le_mul_of_one_le_left hx.le (by norm_num : (1:ℝ) ≤2)); have hψ:=tonicP b O K hp he hV hw t B Q d 1 hx hB hd zero_lt_one h0 -- order F
   have hu :1< Quotes.preExponent p:=by rw [Quotes.preExponent,h0]; linarith
   obtain ⟨p',hz⟩:= Project.orient b p hu (hx.trans_le hB) Q
   have hF:=flash_top p.B; have hF₁:= hF.mul_const (20+8*p'); rw [zero_mul] at hF₁
   filter_upwards [hF.eventually_le_const (show 0<tol/8 by positivity),hF.eventually_le_const (by norm_num : (0:ℝ)<1/64), pureG χ K O p hp h0 he hw t hx, keeps χ p hx g N, chargeQ b true p g hx, chargeQ b false p g hx, hz, hF₁.eventually_lt_const hA, coatP p 8, coatP p (8*p'+4), crownT p.B N,hψ] with c hc0 hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
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
   obtain ⟨X₀,hX,hRz,hω⟩:= pitcherG b p G K U HG s α Q₀ p₀ m 0 hQs h0 hR (hM c) T (h9 s hQs.le hC) hT hv' -- reduce.
   let V:=Finch.scent (c:=c) T p K O p₀ 0 N; let Y:=scoreV G.P G.K p.threshold V (U+m • 1); let A:= bio p X₀ K O U T (p₀+α) Q₀
   have he(i):wearK c N s (Y i)= A i:= hω i
   have hr(j :Bool): tollM j b (A 1)= s^2 * (unitF j c (U 1)+(if j then 0 else m)+μJ j):=by rw [←he, tollM, grassK,map_smul,show unitF j c (fumes b (Y 1))= _ from spoke b V G.P G.K p U m j]; rfl
   refine ⟨X₀,Q₀,s,α,hX,hY.trans_lt h6,?near,hRz,hQs,hQ,by linarith only [hc,hξ],hω,hrg,?_,?_,?_,?_,?_⟩ -- minor
   case near=>
      have hhT: |s-1| *|s+1|≤ tol:=by rw [←abs_mul,show (s-1)*(s+1)=s^2-1 from by ring]; exact hC.trans (by change Φ p.B (-7/4) c ≤ tol/8 at hc0; linarith only [hc0])
      have hpT:1 ≤ |s+1|:= le_trans (by linarith : 1 ≤ s+1) (le_abs_self _)
      exact (le_mul_of_one_le_right (abs_nonneg _) hpT).trans hhT
   · intro i hi; change mud (A i)≠0; rw [← he,proofM]; unfold Y; rw [ζpt _ _ _ _ _ hi,Coda.term]; exact Complex.exp_ne_zero _
   · change tollM true b (A 1)=_; rw [hr true,if_pos rfl, add_zero]; exact hL
   · change tollM false b (A 1)=_; rw [hr false,if_neg (by decide)]; exact hN
   · rw [show Roll T p K O A= Roll _ _ _ _ Y from (funext (fun i=>by unfold Roll glaze; rw [← he,proofM]))]; rw [show (p₀+α)*φ=p₀*φ+e₁ from (by unfold α; field_simp)]; exact PrismT.scroll h1 h2 (show Lab0 su c p χ p₁ from hH) (le_trans (mul_le_mul_of_nonneg_left (le_abs_self M) (abs_nonneg p₀)) (mul_le_mul_of_nonneg_right (hp.trans (le_abs_self W)) (abs_nonneg M))) -- eff mul_le needs lower M. fix.
   refine ⟨lt_min hH.1 (lt_min h1.upT h2.upT),fun i hi=>hH.2 i ⟨hi.1,hi.2.trans (min_le_left ..)⟩⟩
end PrismT
end YM.QCD.High
#print axioms YM.QCD.High.PrismT.evenings
