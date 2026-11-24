import YM.Bank.Palm
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Jule
open Function Lattice Laurent Bloch Metric Filter Finset Next.Free
open Jump Zoom Bee Osc Pilot Pap Palm Kith Murmur Cent Horse
open MeasureTheory InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.L2Operator NNReal ENNReal ContDiff ComplexConjugate
open QCD.Pearl (beamP beam0 beamH)
variable {e b s r t:ℝ}{c:Side} {k j n:ℕ}{L:recordL} {p:Momentum}
def Oasis (a b:ℝ): Set E4 := closedBall 0 b ∩ (ball 0 a)ᶜ
lemma consp {x:E4}(h:x∈Oasis e b):e ≤ ‖x‖∧ ‖x‖≤ b:=⟨by have hx:=h.2; simpa [Set.mem_compl_iff] using hx, by simpa using h.1⟩
lemma door {x:E4}(h:x∈Oasis e b)(he:0<e) :x ≠0:= norm_pos_iff.mp (he.trans_le (consp h).1)
lemma ripple (l:List Axis)(k:ℕ)(b:ℝ)(hr:0<r) {ε:ℝ}(he:0<ε):∀ᶠ s:ℝ in atTop,∀ x:E4,x∈ Oasis r b→ s^k*‖lively l s⁻¹ x-current l x‖≤ε :=by
    obtain ⟨n,F,Z,hZ,H⟩:=spr l; let V:= Oasis r b
    have hv : IsCompact V:= (isCompact_closedBall ..).inter_right (isOpen_ball.isClosed_compl)
    choose C HC using fun i=> hv.bddAbove_image (fun x (hx:x∈ V)=> ((hZ i x (door hx hr)).continuousAt.norm).continuousWithinAt)
    let W i (s:ℝ) := C i * (s^(k+F i)*Real.exp (-(r^2/4)*s))
    have hh i:Tendsto (W i) atTop (𝓝 0):=by simpa only [W,mul_zero,Real.rpow_natCast] using! (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (↑(k+F i)) _ (show 0<r^2/4 by positivity)).const_mul (C i)
    filter_upwards [eventually_gt_atTop (0:ℝ), (show Tendsto (fun s=>∑ i,W i s) atTop (𝓝 0) by simpa using tendsto_finsetSum univ (fun i _=>hh i)).eventually (gt_mem_nhds he)] with s hs he
    intro x hx; rw [H s x (door hx hr),norm_mul,Complex.norm_real,wink,Real.norm_of_nonneg (Real.exp_pos _).le,← mul_assoc]; apply le_trans _ (show ∑ i,W i s ≤ ε from le_of_lt he)
    have hp : Real.exp (s*(-‖x‖^2/4)) ≤ Real.exp (-(r^2/4)*s):= by apply Real.exp_le_exp.mpr; have he := pow_le_pow_left₀ hr.le (consp hx).1 2; nlinarith
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity : 0≤ s^k)) (norm_sum_le ..) (norm_nonneg _) (by positivity)).trans; rw [mul_sum]; apply sum_le_sum; intro i _;
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hs.le]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show ‖Z i x‖≤ C i from HC i (Set.mem_image_of_mem _ hx)) (by positivity : 0≤s^F i)) (by positivity)).trans_eq (by unfold W; ring)
def metricL (L:recordL)(x:E4):= ∑ l∈L.support,L l*current l x
def metricρ (L:recordL)(s:ℝ)(x:E4):= ∑ l∈L.support,L l*lively l s x
lemma costly (L:recordL)(k:ℕ)(b:ℝ)(hr:0<r):∀ᶠ s:ℝ in atTop,∀ x∈Oasis r b,s^k * ‖metricρ L s⁻¹ x-metricL L x‖ ≤ ∑ l∈L.support,‖L l‖:=by
    have h:= (eventually_all_finset _).mpr (fun l (_:l∈L.support)=> ripple l k b hr (ε:=1) zero_lt_one)
    filter_upwards [h,eventually_gt_atTop (0:ℝ)] with s hs hp x hx; unfold metricρ metricL; rw [←sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg hp.le _)).trans; rw [mul_sum]; apply sum_le_sum; intro l hl; rw [←mul_sub,norm_mul,mul_left_comm]; exact mul_le_of_le_one_right (norm_nonneg _) (hs l hl x hx)

def vault (L:recordL)(t:ℝ)(x p:E4) := sound x p *stunted t L (fly p)
lemma stored (L:recordL) (ht:0<t) (x:E4): Integrable (vault L t x) ∧ (x ≠0→ normer • (∫ p,vault L t x p)=metricρ L t x) :=by
    have he : vault L t x = fun p=> ∑ i∈L.support,L i*shine t i x p:=by
       funext p; unfold vault stunted crewG shine χ field; rw [Finset.sum_mul,Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [blown,axle_p,Complex.ofReal_div]; ring
    have hS i : Integrable fun p=> L i*shine t i x p:= (shore ht i x).const_mul _
    rw [he]; refine ⟨integrable_finsetSum _ (fun i _=> hS i),fun h=>?_⟩
    rw [integral_finsetSum _ (fun i _=>hS i),Finset.smul_sum]; apply sum_congr rfl; intro i hi; rw [integral_const_mul, ← mul_smul_comm,show normer • (∫ p, shine t i x p)=_ from nebula i x h ht]; rfl
lemma scaled {x:E4}(h:steady L k) (ht:0<t)(hp:x≠0):
    t^(k+3) • (normer • (∫ p,vault L t (t • x) p))=metricρ L t⁻¹ x:=by
    rw [(stored L ht _).2 (smul_ne_zero ht.ne' hp),metricρ,Finset.smul_sum]; apply sum_congr rfl; intro i hi; rw [deed _ hp ht, ← mul_smul_comm,smul_smul,h i hi,show 2+(k+1)=k+3 by omega,mul_inv_cancel₀ (pow_ne_zero _ ht.ne'),one_smul]
lemma fade (L:recordL)(k:ℕ):∀ᶠ s:ℝ in atTop,∀ x:E4,s^k*‖(∫ y,vault L s x y)-(∫ y in coast,vault L s x y)‖≤1:=by
   let F:=fun y:E4=> ‖stunted 1 L (fly y)‖
   have hx L t (x p): ‖vault L t x p‖ = ‖stunted t L (fly p)‖:=by rw [vault,norm_mul,sounded,one_mul]
   have hF:Integrable F:= (stored L zero_lt_one (0:E4)).1.norm.congr (Eventually.of_forall (fun _=> hx L 1 0 _)); let A:=∫ x in coastᶜ,F x
   have he : Tendsto (fun s:ℝ=> Real.exp (1-s)*(A*s^k)) atTop (𝓝 0) :=by
         have hp:= tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (↑k) 1 zero_lt_one; simp only [Real.rpow_natCast,neg_one_mul] at hp
         refine (show Tendsto _ atTop (𝓝 0) from ?_) -- change
         rw [show (fun s:ℝ=> Real.exp (1-s)*(A*s^k))=fun s=> Real.exp 1*A*(s^k*Real.exp (-s)) by ext; rw [sub_eq_add_neg,Real.exp_add]; ring]; simpa only [mul_zero] using! (hp.const_mul (Real.exp 1*A))
   filter_upwards [eventually_gt_atTop (1:ℝ),he.eventually (gt_mem_nhds one_pos)] with s hh hs; intro x
   have hg (x:E4)(h: x∈coastᶜ) : 1≤ ‖x‖:=by
        have hx:x∉coast:=h; unfold coast at hx; simp only [Set.mem_setOf_eq] at hx; obtain ⟨i,hi⟩:=not_forall.mp hx; apply le_trans (b:= |x i|) ((not_lt.mp hi).trans' (by linarith [Real.pi_gt_three])); exact PiLp.norm_apply_le x i
   have hi:= (stored L (one_pos.trans hh) x).1
   rw [show (∫ y,vault L s x y)-(∫ y in coast,vault L s x y)=∫ y in coastᶜ,vault L s x y by nth_rw 1 [← integral_add_compl hollow.measurableSet hi]; simp]; refine le_trans ?_ (le_of_lt (show Real.exp (1-s)*(A*s^k)<1 from hs))
   apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm ..) (pow_nonneg (zero_lt_one.trans hh).le _)).trans
   rw [show _*(A*s^k)=s^k*(Real.exp (1-s)*A) by ring, show Real.exp (1-s)*A=_ from (integral_const_mul (Real.exp (1-s)) F).symm]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_lt_one.trans hh).le _)
   apply setIntegral_mono_on hi.norm.integrableOn ((hF.const_mul _).integrableOn) hollow.measurableSet.compl; intro p hp
   have hq:= hg p hp; rw [hx]; unfold F stunted; rw [norm_mul,norm_mul,mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
   rw [Complex.norm_exp,Complex.norm_exp,axle_p]; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; simp; rw [← Complex.ofReal_pow,Complex.ofReal_re]; nlinarith [show 1≤‖p‖^2 by nlinarith]
lemma vault_r (L:recordL)(t:ℝ)(z:Cover)(ht:0<t)(hs:steady L k)(σ:Bool):Tendsto (fun n:Side=> QCD.Pearl.beamH n^4 • Horse.summit n z σ (stunted t L ∘ grid σ)) atTop (𝓝 (∫ x in coast,vault L t (rock z) x)):=by
   have hu p (hP:p∈coast) (hx:p ≠(0:E4)): ContinuousAt (vault L t (rock z)) p:=by
       apply (Continuous.continuousAt (f:=sound (rock z)) (by unfold sound; fun_prop)).mul;
       have hp: fly p≠0:=by intro h; have hi:=congr_arg axle h; rw [axle_nil,axle_p] at hi; simp [hx] at hi
       exact (((stellar L hs ht.le (fly p) (by exact ⟨scope_p _,fun i=> (show _ ≤ _ from (hP i).le)⟩) hp (fly p) (mem_ball_self (mul_pos ans (norm_pos_iff.mpr hp)))).1).continuousAt).comp born_p.continuousAt -- p in coast needed
   let A:=betaL L k*Real.pi^k; have hA:0≤ A:= mul_nonneg (beta_pos ..) (pow_nonneg Real.pi_pos.le _)
   have ht (c:Side)(i:Site c): ‖vault L t (rock z) (earth (grid σ i))‖≤ A/‖grid σ i‖:=by
       let p:=grid σ i; have hp:=cubic σ i; unfold vault; rw [trim_p _ hp.1,norm_mul,sounded,one_mul]; by_cases h:grid σ i=0; rw [h,(zero_f L t).2,norm_zero,norm_zero,div_zero]; exact (stellar L hs ht.le _ hp h _ (mem_ball_self (mul_pos ans (norm_pos_iff.mpr h)))).2
   apply (follows σ hA _ (fun x hx hX=> hu x hx hX) ht).congr'; apply Eventually.of_forall; intro n; unfold Horse.summit; dsimp only; rw [Finset.smul_sum]; refine sum_congr rfl fun i _=>?_; unfold vault; rw [hits_e,trim_p _ (cubic ..).1]; rfl
end YM.Bank.Jule
#print axioms YM.Bank.Jule.vault_r
#print axioms YM.Bank.Jule.fade
