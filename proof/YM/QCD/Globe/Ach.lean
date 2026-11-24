import YM.QCD.Globe.Lunch
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Nola Brick
variable (P:Plan 4)(L B:Side)(i:Flavor N)
variable {V T t v r W d a x w:ℝ}
lemma panelL (p: Matrix (Modes c N) (Modes c N) ℂ)(X: EvenA c N)(k:ℕ): Stew.stage k (sways p X)=sways p (Stew.stage k X):=Subtype.ext (sport p X.val _)
lemma peaked (X:EvenA c N)(hp:Cocoa X):Cocoa (oilD X):=by
   apply Cocoa.sub hp; -- diag
   refine ⟨fun i h=>?_,fun p=>?_,fun p g z h=> ?_,?_⟩
   · rw [←panelL,hp.flavorG _ h]
   · rw [←panelL,hp.choco _]
   · exact (panelL _ X 0).symm.trans (congr_arg (Stew.stage 0) (hp.cream p g z h))
   apply Subtype.ext; change disguise _ (surf _ (panel 0 X.val))= _; rw [←toned X.val,←Stew.sport]; exact congr_arg (panel 0) (congr_arg Subtype.val hp.real)
lemma mantle (X:EvenA c N) (A: Sheet c)(K:EvenA c N)(hp:wearK c N w (exp (paleF N A+oilD X))=exp K)(hw:0<w)(he:w≤ 2)(h:GrassA X t m a)(ht:0<t): let j:ℝ:= (2*(Fintype.card Fiber:ℝ)*N)*Real.log 2 + a; expo j c*pebble K ≤ pebble (paleF N A+ X):=by
   intro j; let Y:=paleF N A+oilD X
   let f:=UPr X; let R:=Real.exp f.re
   have hs: expo a c ≤ R:=by
       apply Real.exp_monotone; have hQ:= (abs_le.mp ((Complex.abs_re_le_norm _).trans (massB X ht h))).1; linarith only [hQ] -- f defeq
   have he':pebble (paleF N A+X)=R*pebble Y:=by
       unfold pebble; rw [oaks, show Y=_ from rfl,ring_of X, Algebra.mul_smul_comm, map_smul,norm_smul,Complex.norm_exp]; exact congr_arg _ ((congr_arg (fun x=> ‖ber _ x‖) (oaks (oilD X) A).symm)) -- syntax
   let F:=Rain.gain w c N
   have ht:pebble K =F*pebble Y:=by unfold pebble; rw [show exp K.val=Cove.light _ (wearK c N w (exp Y)) from hp.symm ▸ (Cove.light_exp K).symm,Rain.crestP,norm_mul, Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ Rain.gain w c N from pow_nonneg hw.le _)]; exact congr_arg (F*·) (congr_arg (‖·‖) (show Rain.peakW c N (exp Y)= _ from congr_arg (ber _) (Cove.light_exp Y))) -- syntax
   let z₀:ℝ:=2*(Fintype.card Fiber:ℝ)*N*Real.log 2; have hx:expo z₀ c*F ≤1:=by
       have hg : (Fintype.card (Keys c N):ℝ)=Fintype.card (Site c)*(2*(Fintype.card Fiber:ℝ)*N):=by simp [Row,Keys,Modes,Pairs,Flavor]; ring
       unfold F Rain.gain; refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw.le he (Fintype.card (Keys c N))) (Real.exp_pos _).le) ?_
       rw [show (2:ℝ)= Real.exp (Real.log 2) from Eq.symm (Real.exp_log (by norm_num)), ← Real.exp_nat_mul, expo, ← Real.exp_add,hg]; unfold z₀; ring_nf; simp
   rw [show expo j c=expo z₀ c*expo a c from ?_,he', ht,mul_right_comm (expo z₀ c),← mul_assoc]; rotate_left -- inspect
   · unfold expo j z₀; rw [mul_add,Real.exp_add]
   -- price transform
   rw [mul_right_comm _ (pebble Y)]; apply mul_le_mul_of_nonneg_right _ (show 0 ≤ pebble Y from norm_nonneg _); exact (mul_le_of_le_one_left (Real.exp_pos _).le hx).trans hs
lemma origins (K':ℕ) (c:Side) (B:ℕ) (hh:B ≤ c.val)(u:Train 4)(Z: EvenA c N) (M:Sheet c)(Y:ℝ)(hp:K'=N) (hz:Cocoa Z)(h: Mercy i 6 T)(ht: GrassA Z (2*t) 6 a)(ht':a≤d)(hd:0<t)(hv:Fintype.card (Site c)>0)(hr:0 ≤r)(hf:1/2 ≤ sheen M)(hM: Tempo M)(hY:Beam M 6 V)(hV:0≤V)(hw:(2*t)⁻¹^2*T*a ≤ x)(he:0≤x)(hh':x≤1/4) (hq:2*dimeZ V x ≤r)(hy:dimeZ V x ≤ v) (hhU: M=sunny P u c) (hW: Wins P c N t r d v W):expo ((2* (Fintype.card Lat.Fiber:ℝ)*N)*Real.log 2 +a+W) c ≤ pebble (paleF N M+Z):=by
    let X:=oilD Z; let H:=feeF i X; let G:=peakZ X; have ht₀:0<2*t:=by positivity
    have h0: GrassA X (2*t) 6 a:= (cardsY Z ht ht₀).1; have hQ:= peaked Z hz; obtain ⟨w',_,hJ,hU,O,A',hk⟩:=lin G (by rw [show G=X-paleF N H from Eq.symm (by nth_rw 1 [mercyR X i (oil₀ Z) hQ.flavorG]; exact add_sub_cancel_left ..)]; exact hQ.sub ((hQ.pick i).butter _)) (Globe.forged _) ((show GrassA G (2*t) 6 d from le_trans ((cardsY X h0 ht₀).2) (mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg _)))) hd M H hM (hQ.pick i) hY ((h _ _ _ _ ht₀ hQ h0).up hw) he hV hf hh';
    let A:= dub M H w'; let F:= wearK c N w' G
    have hu: Fused F A t r d:=⟨hk.tone,hk.rateG,hk.remS.up hq,hk.cocoa,hk.moo,hk.work⟩
    let Z':= paleF N (M+A)+F; have he' : wearK c N w' (exp (paleF N M+oilD Z))=exp Z':=by apply Eq.trans _ O; congr 2; rw [Port.oneC]; rw [add_assoc]; exact congr_arg _ (mercyR X i (oil₀ Z) hQ.flavorG) -- fix
    have Hc:=mantle Z M Z' he' hJ hU ht ht₀
    have hK: expo W c ≤ pebble Z':=by unfold Z'; rw [hhU]; exact hW.per F u A hu (A'.trans hy)
    unfold expo; rw [mul_add,Real.exp_add]; exact le_trans (mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le) Hc
-- master
end YM.QCD.Globe
