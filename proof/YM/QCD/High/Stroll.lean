import YM.QCD.High.Nark
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
local notation "S0"=>EvenA c N
lemma another (k:Finset (Keys c N))(x:S0)(h:mud x=0)(hh:k.card<2):coef k x.val=0:=by
    by_cases hp:k=∅; · subst k; exact h
    exact measured k (by have h': k.card ≠0:= mt Finset.card_eq_zero.mp hp; omega) _
lemma lossM (k:Finset (Keys c N))(hp:k.card≤2) (x y:S0)(hx:mud x=0)(hy:mud y=0):coef k (x*y).val=0:=by
   change coef k (x.val*y.val)=0; rw [← write x.val,←write y.val, Finset.mul_sum,map_sum]; refine sum_eq_zero fun i _=>?_ ; rw [Finset.sum_mul,map_sum]; refine sum_eq_zero fun j _=>?_
   by_cases h:i.card<2; · rw [another i y hy h,zero_smul,mul_zero,map_zero]
   by_cases hz:j.card<2; · rw [another j x hx hz,zero_smul,zero_mul,map_zero]
   rw [smul_mul_smul_comm,map_smul]; rw [show coef k (mono j*mono i)=0 from ?_,smul_zero]
   by_cases hk : Disjoint j i; swap; · rw [mono_mul_zero _ _ hk, map_zero]
   let Q:=j.disjUnion i hk; have he: k≠ Q:=ne_of_apply_ne Finset.card (show k.card≠ Q.card from by rw [show Q.card=j.card+i.card from card_disjUnion ..]; omega)
   rcases mono_mul_sign j i hk with hu|hu; · rw [hu,Grass.read_other _ _ he]
   rw [hu,map_neg,Grass.read_other _ _ he,neg_zero] -- edit map_neg
lemma held (x:S0)(k:ℕ)(hx:mud x=0)(hk:1 ≤ k): mud (x^k)=0:=by
   induction k,hk using Nat.le_induction with
   | base => rw [pow_one]; exact hx
   | succ k hk ih=> rw [pow_succ]; exact lossM ∅ (by simp) _ _ ih hx
lemma loses (x:S0)(hx:mud x=0)(k:ℕ)(hp:2≤k):meter b (x^k)=0:=by
   cases k with
   | zero => omega
   | succ k=> ext i j; rw [pow_succ]; change bit (i,b) (j,b)*coef (Stew.tag _ _) ((x^k*x).val)=0; rw [lossM _ (by simp [tag]) _ _ (held x k hx (by omega)) hx,mul_zero]
lemma begins :meter (c:=c) b 1=0:=by
   ext i j; change bit (i,b) (j,b)*coef _ (1:Dirac _)=0; rw [← Grass.mono_empty]; rw [read_other,mul_zero]; simp [Stew.tag]
lemma proud (x:S0)(hx:mud x=0):meter b (exp x)=meter b x:=by
   let M:=meter (c:=c) b; let g(k:ℕ):= M ((k.factorial:ℂ)⁻¹ • x^k); have h : HasSum g (M (exp x)):= M.hasSum (exp_series_hasSum_exp' (𝕂:=ℂ) x)
   rw [← show (∑' i,g i)=_ from h.tsum_eq]; rw [tsum_eq_single 1]; · unfold g; simp; rfl -- edit
   intro i hi; by_cases hp:i=0; · subst i; unfold g; rw [pow_zero,map_smul,begins,smul_zero] -- let M
   unfold g M; rw [map_smul, PrismT.loses b x hx i (by omega), smul_zero]
-- obs normalized by scalar body.Oct.Exp.Log.Exp.Global uses |.|.
noncomputable def fumes (x : S0): Sheet c:= (mud x)⁻¹ • meter b x
lemma lively (x:S0) : fumes b (exp x)=meter b x:=by
    let y:=sparkF c N (mud x); have h0:clay c N y=mud x:=by change clay c N (mud x • 1)=_; rw [map_smul,show clay c N 1=1 from ?_,smul_eq_mul,mul_one]; change coef ∅ (1:Grass.Alg _) =1; rw [←mono_empty,Grass.read]
    have he : mud (x-y)=0:=(map_sub (clay c N) ..).trans (h0 ▸ sub_self _)
    have hp:meter b y=0:=by unfold y sparkF; rw [map_smul,begins,smul_zero]
    unfold fumes; rw [Coda.term]; rw [show exp x=exp y*exp (x-y) from (Eq.trans (by rw [show y+(x-y)=x by abel] : exp x=exp (y+(x-y))) (exp_add ..)),show exp y=sparkF c N _ from sky_first ..]; unfold sparkF; rw [smul_mul_assoc,one_mul,map_smul,proud b (x-y) he,map_sub,hp,sub_zero,smul_smul,inv_mul_cancel₀,one_smul]; exact Complex.exp_ne_zero _
lemma grassK (v:ℝ)(x:S0): fumes b (wearK c N v x)= v^2 • fumes b x:=by unfold fumes; rw [Kites.proofW,proofM,← Complex.ofReal_pow]; exact smul_comm ..
lemma fogL (u: ℝ)(x:S0)(he:0<u): fumes b (u • x)=fumes b x:=by
   change fumes b ((u:ℂ) • x)=_; unfold fumes; change (clay c N ((u:ℂ) • x))⁻¹ •(meter b ((u:ℂ) • x))=_; rw [map_smul,map_smul,smul_eq_mul,mul_inv_rev, smul_smul,mul_assoc,inv_mul_cancel₀ (by exact_mod_cast he.ne'),mul_one]; rfl
end PrismT
end YM.QCD.High
