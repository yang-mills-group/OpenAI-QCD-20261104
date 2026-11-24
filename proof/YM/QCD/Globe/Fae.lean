import YM.QCD.Globe.Mark
import YM.QCD.Rain.Zen
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
open Nola
variable {a b t T w:ℝ}
lemma detRun (X:Sheet c)(hp:IsUnit X.det)(he:Beam X⁻¹ m a)(ha:0<a): a⁻¹^Fintype.card (Row c)≤ ‖X.det‖:=by
    let g x y:=costS m x y*‖cell X⁻¹ x y‖
    have h: ‖X⁻¹‖≤ a:=by
        apply wind_op ha.le _ g (fun i j=> ?_) he.toR (fun j=> ?_); · exact le_mul_of_one_le_left (norm_nonneg _) (cost_one ..)
        have h:= he.axR j; unfold Gan at h; simp_rw [cell_flip,norm_star,id_eq,cost_symm j _] at h; exact h
    apply Cost.min_det _ (inv_pos.mpr ha).le; intro x
    have hx:= (Cost.op X⁻¹).le_opNorm (Cost.op X x); rw [← Matrix.cstar_norm_def,← mul_apply_eq_comp,← map_mul,Matrix.nonsing_inv_mul X hp,map_one,one_apply_eq_self] at hx; rw [inv_mul_eq_div,div_le_iff₀ ha]; exact hx.trans ((mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (mul_comm ..))
def expo (a:ℝ)(n:Side):ℝ:= Real.exp (-(Fintype.card (Site n):ℝ)*a)
lemma detRatio (X:Sheet c)(hp:IsUnit X.det)(he:Beam X⁻¹ m a)(ha:0<a)(N:ℕ):expo ((Fintype.card Fiber:ℝ)*N*Real.log a) c ≤ ‖X.det^N‖:=by
    have ht :=detRun X hp he ha; apply le_trans _ (le_of_le_of_eq (pow_le_pow_left₀ (show 0 ≤ a⁻¹^Fintype.card (Row c) by positivity) ht N) (norm_pow X.det N).symm); unfold expo Lat.Row; rw [ ← show Real.exp (-(Real.log a))=a⁻¹ from ?_,← Real.exp_nat_mul,← Real.exp_nat_mul]; · rw [Fintype.card_prod (Site c) Lat.Fiber]; push_cast; exact le_of_eq (by ring_nf)
    rw [Real.exp_neg,Real.exp_log ha]
lemma massB (Z:EvenA c N)(hp:0<t)(ht:GrassA Z t m a):‖UPr Z‖ ≤ Fintype.card (Site c)*a:=by
    refine le_trans (b:=band locationP Z.val t m) ?_ ht; refine (le_trans ?_ (single_le_sum (s:=univ) (f:=grainH locationP Z.val t m) (fun x _=> grains _ Z.val hp x) (mem_univ ∅))); simp only [grainH,UPr,card_empty,pow_zero,mul_one]; exact le_mul_of_one_le_right (norm_nonneg _) (tell_one ..)
noncomputable def pebble (X:EvenA c N):ℝ:= ‖ber _ (exp X.val)‖
lemma fanfare (M:Sheet f) (L: EvenA c N)(X:EvenA f N)(Q:Matrix (Modes c N) (Modes f N) ℂ)(Y Z:EvenA c N)(h: Beam M⁻¹ m a)(ht:IsUnit M.det)(ha: 1 ≤ a)(hel:GrassA L t j b)(hs: 0 ≤ b)(hp:0<t)(he:sheath 1 Q (exp X.val)=(M.det^N*Complex.exp (UPr L)) • exp Y.val)(hf: wearK c N w (exp Y)=exp Z)(hw:0<w)(hh:w≤2)(hr:c ≤ f): let v:ℝ:=Fintype.card (Site f); expo ((Fintype.card Fiber:ℝ)*N*Real.log a+b+ (2*(Fintype.card Fiber:ℝ)*N)*Real.log 2) f * pebble Z ≤ pebble X:=by
    let n:=Fintype.card (Site f); let d:=Fintype.card (Site c); have hr' :(d:ℝ)≤(n:ℝ):=Nat.cast_le.mpr (by unfold d n; rw [site_card,site_card]; gcongr; exact hr)
    have hK: pebble Z= Rain.gain w c N*pebble Y:=by unfold pebble; rw [show exp Z.val=Cove.light _ (wearK c N w (exp Y)) from hf.symm ▸ (Cove.light_exp Z).symm,Rain.crestP, norm_mul, Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ Rain.gain w c N from pow_nonneg hw.le _)]; exact congr_arg _ (congr_arg (‖·‖) (show Rain.peakW c N (exp Y)=_ from congr_arg (ber _) (Cove.light_exp Y))) -- syntax
    have hn:2^(Fintype.card (Keys c N):ℕ) ≤ Real.exp ((n:ℝ)*(2*(Fintype.card Fiber:ℝ)*N*Real.log 2)):=by
         rw [show (2:ℝ)=Real.exp (Real.log 2) from Eq.symm (Real.exp_log (by norm_num))]; -- also RHS replaced
         rw [← Real.exp_nat_mul,Real.log_exp]; apply Real.exp_monotone
         have he : Fintype.card (Keys c N)=2*(d*(Fintype.card Fiber)*N):=by simp [Keys,Modes, Row, Flavor, Pairs,d]; ring
         rw [he, Real.exp_log (by norm_num)]; push_cast; nlinarith only [mul_le_mul_of_nonneg_right hr' (show 0≤ 2*(Fintype.card Fiber:ℝ)*N*Real.log 2 by positivity)]
    let k:= (Fintype.card Fiber:ℝ)*N*Real.log a; let r:=2*(Fintype.card Fiber:ℝ)*N*Real.log 2; let q:= Rain.gain w c N; intro v
    have hz:expo r f*q ≤ 1:=by
         unfold q Rain.gain; apply le_trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hw.le hh _).trans hn) (Real.exp_pos _).le); unfold r n; simp [mul_assoc,← Real.exp_add, neg_mul]; -- association
    have he' : expo r f *pebble Z ≤ pebble Y:= by rw [hK,←mul_assoc]; exact mul_le_of_le_one_left (norm_nonneg _) hz
    have hB: expo b f ≤ ‖Complex.exp (UPr L)‖:=by rw [Complex.norm_exp]; unfold expo; apply Real.exp_monotone; have hy: |(UPr L).re|≤n*b:= (Complex.abs_re_le_norm _).trans ((massB L hp hel).trans (mul_le_mul_of_nonneg_right hr' hs)); linarith only [(abs_le.mp hy).1] -- n unfold
    have hh': pebble X= ‖M.det^N‖ * ‖Complex.exp (UPr L)‖ * pebble Y:=by unfold pebble; rw [←Kit.insulate (by norm_num : (1:ℝ) ≠0) Q (exp X.val), he,map_smul,norm_smul,norm_mul]
    change expo (k+b+r) f * _ ≤ _; rw [show expo _ _= expo k f *expo b f*expo r f from ?_, mul_assoc, hh']; exact mul_le_mul (mul_le_mul (detRatio M ht h (zero_lt_one.trans_le ha) N) hB (Real.exp_pos _).le (norm_nonneg _)) he' (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) -- assoc
    unfold expo; rw [mul_add,mul_add,Real.exp_add,Real.exp_add]
end YM.QCD.Globe
