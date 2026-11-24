import YM.QCD.High.Foliage
import YM.QCD.Fall.Bend
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
open Acre Acre.Rails
local notation "rK" => (1/8:ℝ)
variable {L:Side}{x C P' :ℝ}
section enn
variable (G:Gem c N ι)(F:Patron.Rail c N β)[Countable ι][Countable β]
-- adaptive promise without face beyond
lemma levy (hp: Crossing G)(hΩ:MixedP F)(hh:Wick G)(hK: Quanta G b)(hX: F.Reg p.threshold)(hE:Licence p t (Jets.Touch.chip L x) (fan L η x) G)(hF: Quits F p.B 1 (taxK L x 1) t (fan L η x))(hb:p.B=highR L x)(hv:0≤t): Enn p b L x η t (duo G F):=by
   let W':=duo G F; obtain ⟨f,hf,hϕ⟩:= hE.zone; obtain ⟨g,hg,hQ⟩:= hF.cost; have he :0≤g:=fun i=>(norm_nonneg _).trans (hQ i 1); let θ:=fan L η x
   have hL:0<θ:=fan_pos ..; refine ⟨f,g,⟨⟨fun i=>(hϕ i).travel,he,?_,hQ⟩,⟨hv,(Real.exp_pos _).le, ?_,?fill⟩,regimen _ _ (Licence_g hE) hX,painted G F hp hΩ p.threshold⟩,?gift⟩
   · intro i U; change Creek.load _ (light _ (masked p.threshold (G.addr i).support _ U))≤_; by_cases ht:Healthy p.threshold (G.addr i).support U
     · rw [masked_eq _ _ _ _ ht]; exact (shot (lens (G.addr i).site) _ θ hL).trans ((hϕ i).sizeU U ht)
     rw [masked_ne _ _ _ _ ht,map_zero,load_zero]; exact (hϕ i).travel
   · rw [← hb]; intro i; refine budget_mono (hf i) ?_ ?_
     · intro j; split <;> first| exact mul_nonneg (hϕ j).travel (Real.exp_pos _).le| exact le_rfl
     intro j; by_cases hv:(G.addr j).site=i
     · change ite ((G.addr j).site=i) _ _ ≤ _; rw [if_pos hv,if_pos hv]; exact le_rfl
     exact (if_neg (show ¬ (W'.row j).site=i from hv)).le.trans ((hf i).1 _)
   case fill=>
      rw [← hb]; rw [show (fun i => _)=GasP.taxed (Ruby.oriD F) g (taxK L x 1) from ?_]; · exact hg
      funext i; exact mul_comm ..
   case gift=>
     intro i; have hp₁:= hp.blank; refine ⟨hϕ i,fun hi=> ⟨hϕ i,hp₁.gauge i,hp₁.num i,hp₁.real i,hK i hi,⟨(spores _ _ _ (hϕ i) (hp₁.gauge i) hL.le).1,(G.addr i).anchor, ?_,fun _ x y hx hy=> (hh i hi).2 x y hx hy⟩⟩⟩; change -(mud (G.view i 1)).re = 0; rw [(hh i hi).1]; simp
end enn
variable (p:BudgetPoint)(S:Voice c N)(K:PathData su) (X:St c)
section indicated
variable {Q:Stage}(h:Glory L p b η x 1 S)(s α ν β₀ m v v':ℝ)(hv:0<s)(ht:p.supportExponent=2)(he:p.B=highR L x)
variable (hV:∀ (I V:Type)(Y:Ruby.Hue c N I)(X: Patron.Rail c N V), Quits X p.B 1 (taxK L x 3) (rK+rK) (fan L η x) → Purchases Y p.threshold p.B (rK+rK+1) 1 (fan L η x) → Quits (Ruby.Trail Y X p.threshold) p.B 1 (taxK L x 1) rK (fan L η x))
local notation "E!"=> Jets.Touch.chip L x
set_option quotPrecheck false
lemma bdH (J:ℕ→ Atom su 2) : baker c N ∘ Finch.scent (c:=c) J p K O β₀ v N-baker c N ∘Finch.scent J p K O (β₀+α) v N=α • topsK K O p c N:=by
   funext U; dsimp only [comp_apply, Pi.sub_apply,Pi.smul_apply]; rw [← map_sub]; apply Eq.trans (b:=baker c N (α • Push.BetaTransport.kinetic K O p U)) (congr_arg _ _); · exact map_smul _ _ _
   unfold scent Reggae.pulse; rw [channels_split (D:=K) _ β₀,channels_split (D:=K) _ (β₀+α)]; rw [smul_eq_mul]; ring
include hV h he hv ht
lemma publishG (J:ℕ→Atom su 2)(hz: Steep c N s)(hQ:1 ≤ fan L η x)(hy: Feat (back α (s^2-1) (s^2*m-ν) K O p X N) p b (fan L η x) (rK+rK+1) (E!-Real.exp (-1)*(E!)) 1):∃ A:Voice c N, Enn p b L x η rK (duo A.P A.K) ∧∀ (V: Grid c), wearK c N s (scoreV S.P S.K p.threshold (Finch.scent J p K O β₀ v N) (X+m • 1) V)= scoreV A.P A.K p.threshold (Finch.scent J p K O (β₀+α) v N) (X+ν • 1) V:=by
   obtain ⟨I,Y,hI,hY,B,D,W⟩:=hy; let r:=fan L η x; let E:=flightE S.P s; let T:=flightK S.K s; let F:=weave E B; let H:=Ruby.Trail D T p.threshold; let Z:=h.portraitP; have hh:Countable (Ruby.Plot D T):=glazeP ..
   have hx:=fan_pos L η x; have hR:rK ≤ rK+rK+1:=by norm_num
   have hℓ:Licence p rK (Real.exp (-1)*(E!)) r E:=greys S.P hz (by rw [← ht]; exact Z.quoteE) hv hx
   have hh' :Licence p rK (E!) r F:=scoreH F (guardL E B hℓ (wells B W.waveP hR le_rfl)) (by linarith)
   have hk:= verses S.K hz (p:=p) Z.quoteK hv hx (Real.exp_pos _).le; have hy:Rise.Wave (duo S.P S.K) p.threshold:=regimen _ _ (Licence_g Z.quoteE) Z.perm
   obtain ⟨hX,hL⟩:=gustK S.K Z.passK Z.perm s; obtain ⟨hP,hT⟩:= pears _ _ b Z.pure2 Z.pure1
   have hα₁ :Wick F:=by intro i; cases i; exact fun hi=>⟨hP.face _,hP.van _ hi⟩; exact W.maskG _
   refine ⟨⟨_,_,F,H⟩,levy b F H (pilot _ _ (gustE S.P Z.passE s) W.cover) (Ruby.wheel _ _ W.tax.projection hL _) hα₁ (fibs _ _ b hT W.atoms) (Ruby.plant D T W.tax.life hX) hh' (hV _ _ D T hk W.tax) he (by norm_num),fun U=>?_⟩
   rw [eff S.P S.K U s p.threshold _ (X+m • 1) (Z.boreal U).2 (Z.boreal U).1 rfl]; refine routesC E T D U ?_ W.tax.life ((Kites.heart D W.tax (by norm_num) hQ U).2) (story S.K U s _ (Z.boreal U).2).summable
   rw [heartS,heartS,show _root_.YM.QCD.Patron.total ((⟨_,_,F,H⟩:Voice c N).P) _ _=_ from (woven_sum E B U (t:=p.threshold) (sour S.P U s (Z.boreal U).1).summable (permits B W.waveP hx (by norm_num) U))]; apply Eq.mp (congr_arg (HasSum _) ?eq) (W.eyeG U)
   case eq=>
      have hp:= congr_fun (bdH p K α β₀ v J (O:=O) (c:=c) (N:=N)) U; dsimp only [comp_apply,Pi.sub_apply,Pi.smul_apply] at hp
      simp only [back, Pi.add_apply, Pi.smul_apply, Pi.one_apply,comp_apply]; -- simplifies topsK?
      let M:Sheet c→L[ℝ]EvenA c N:=(nozzle c N).restrictScalars ℝ; have hs : M (s^2 • (X U+m • 1))- M (X U+ν • 1)=(s^2-1) • paleF N (X U)+(s^2*m-ν) • paleF N (1:Sheet c):=by rw [← map_sub]; rw [show s^2 • (X U+m • 1)-(X U+ν • 1)=(s^2-1) • X U+(s^2*m-ν) • 1 from (by rw [smul_add,smul_smul,sub_smul, sub_smul,one_smul]; abel),map_add,map_smul,map_smul]; rfl
      change nozzle c N (s^2 • (X U+m • 1))- nozzle c N (X U+ν • 1)= _ at hs
      rw [← hp,← hs]; abel
end indicated
end YM.QCD.High
#print axioms YM.QCD.High.publishG
