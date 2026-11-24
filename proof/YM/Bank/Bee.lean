import YM.Bank.Peon
/-! Astronomical boards and charges on any pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Bee
open Lattice Laurent Bloch Metric Wilson RG Next.Free Finset Osc Wale Pilot Filter
open Complex (I)
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator ContDiff NNReal ENNReal
variable {c:Side}{σ:Bool}{k:ℕ}{p q:Momentum}{a b r t:ℝ}
def axle (p:Momentum):= ∑ i:Axis,(p i)^2
@[simp] lemma axle_nil:axle 0=0:=by simp [axle]
lemma axle_w (hp:physical p) : axle p=(lengthSq p:ℂ):=by unfold axle lengthSq; rw [Complex.ofReal_sum]; apply sum_congr rfl; intro i _; rw [←inland hp i,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.ofReal_pow]
lemma norm4 (p:Momentum): ∑ i:Axis,‖p i‖^2≤ 4*‖p‖^2:=by apply (sum_le_sum fun i _=> pow_le_pow_left₀ (norm_nonneg (p i)) (norm_le_pi_norm p i) 2).trans_eq; simp [Axis]
def a₀ : ℝ:= 1/96
lemma ans :0<a₀:=by unfold a₀; norm_num
lemma beat (hp:physical p)(h:p≠0)(hq:q∈collar p a₀): ‖q‖≤2*‖p‖∧ ‖p‖^2/2 ≤ (axle q).re :=by
   have hx: ‖q-p‖≤ a₀*‖p‖:= (dist_eq_norm q p) ▸ (mem_ball.mp hq).le
   have he:= norm_pos_iff.mpr h; have ht: ‖q‖≤ 2*‖p‖:=by unfold a₀ at hx; linarith [norm_sub_norm_le q p]
   have hw:‖axle q-axle p‖≤‖p‖^2/2:=by
       simp_rw [axle, ←sum_sub_distrib]; apply (norm_sum_le ..).trans;
       let H:=a₀*‖p‖*(3*‖p‖)
       refine (Finset.sum_le_sum (g:=fun (i:Axis)=>H) fun i _=>?_).trans ?_
       · have hi : ‖q i - p i‖ ≤ a₀*‖p‖:= (norm_le_pi_norm (q-p) i).trans hx; have hj:‖q i+p i‖≤3*‖p‖:=by linarith [norm_add_le (q i) (p i),norm_le_pi_norm q i,norm_le_pi_norm p i]; -- A
         rw [show (q i)^2-(p i)^2=(q i-p i)*(q i+p i) by ring,norm_mul]; exact mul_le_mul hi hj (norm_nonneg _) (mul_nonneg ans.le he.le)
       simp [Axis,H,a₀]; nlinarith
   have hu:= (Complex.abs_re_le_norm _).trans hw; rw [Complex.sub_re, axle_w hp,Complex.ofReal_re] at hu; exact ⟨ht,by linarith [(abs_le.mp hu).1,QCD.Pearl.vector_max p]⟩
-- monomials. list via arbitrary fin sums. astrolabe both hyms in pair on real p.
abbrev recordL:= (List Axis)→₀ℂ
def steady (L:recordL)(k:ℕ):Prop :=∀ i∈L.support,i.length=k+1
def field (l:List Axis)(p:Momentum):= (axle p)⁻¹*barrier p l
def crewG (L:recordL)(p:Momentum):= ∑ i∈L.support,L i * field i p
lemma foil (l:List Axis)(q:Momentum):DifferentiableAt ℂ (fun p=> barrier p l) q:=by induction l with
    | nil=> simp[barrier]
    | cons i l ih=> exact (show DifferentiableAt ℂ (fun p:Momentum=> I*p i) q from by fun_prop).mul ih
lemma listed (u: Momentum) (l: List Axis): ‖barrier u l‖ ≤ ‖u‖^l.length:=by induction l with
    | nil=>simp [barrier]
    | cons a l ih=> simp only [barrier,List.map_cons,List.prod_cons,norm_mul,Complex.norm_I,one_mul,List.length_cons]; rw [pow_succ']; exact mul_le_mul (norm_le_pi_norm _ _) ih (norm_nonneg _) (norm_nonneg _)
lemma shel (L:recordL){p q:Momentum}(h:physical p)(hp:p≠0)(hx:q∈collar p a₀): DifferentiableAt ℂ (crewG L) q:=by
     obtain ⟨_,hb⟩:= beat h hp hx; have hu:= norm_pos_iff.mpr hp; have hz:axle q≠0:=by intro e; rw [e] at hb; simp at hb; nlinarith
     have he := ((show DifferentiableAt ℂ axle q from by unfold axle; fun_prop).inv hz); unfold crewG field; exact DifferentiableAt.fun_sum (fun i _=> (differentiableAt_const _).mul (he.mul (foil i q)))
def betaL (L:recordL)(k:ℕ):ℝ:= ∑ l∈L.support,‖L l‖*2*2^(k+1)
lemma beta_pos (L:recordL)(k:ℕ):0≤ betaL L k:= sum_nonneg fun _ _=>by positivity
lemma vision {L:recordL}(hp:steady L k){p q:Momentum}(h:physical p)(hv:p≠0)(hx:q∈collar p a₀): ‖crewG L q‖≤betaL L k*‖p‖^k/‖p‖:=by
    obtain ⟨he,hQ⟩:=beat h hv hx; have hz:=norm_pos_iff.mpr hv
    unfold betaL; rw [sum_mul,sum_div]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i hi; unfold field; rw [norm_mul,norm_mul,norm_inv]; have hk: ‖p‖^2/2≤ ‖axle q‖:=hQ.trans (Complex.re_le_norm _); have ht:0< ‖p‖^2/2:=by positivity
    exact (mul_le_mul_of_nonneg_left (mul_le_mul ((inv_le_inv₀ (ht.trans_le hk) ht).mpr hk) (show ‖barrier q i‖≤(2*‖p‖)^(k+1) from (listed _ _).trans ((hp i hi) ▸ pow_le_pow_left₀ (norm_nonneg _) he _)) (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans_eq (by rw [mul_pow,pow_succ ‖p‖]; field_simp; ring)

def stunted (t:ℝ)(L:recordL)(p:Momentum):=crewG L p*Complex.exp (-(t:ℂ)*axle p)
lemma stellar (L:recordL)(hp:steady L k)(ht:0 ≤ t)(p: Momentum)(h:p∈baseCube)(h0:p≠0)(v:Momentum)(he:v∈collar p a₀):
      DifferentiableAt ℂ (stunted t L) v ∧ ‖stunted t L v‖ ≤ betaL L k*Real.pi^k/‖p‖:=by
    have hf : DifferentiableAt ℂ (fun x=>Complex.exp (-(t:ℂ)*axle x)) v:=by unfold axle; fun_prop
    refine ⟨(shel L h.1 h0 he).mul hf,?_⟩; unfold stunted; rw [norm_mul];
    have hx:(-(t:ℂ)*axle v).re ≤0:=by
       have ht:=beat h.1 h0 he; have hh:0≤(axle v).re:=by linarith [ht.2, sq_nonneg ‖p‖]
       simp; exact mul_nonneg ‹0≤t› hh
    exact (mul_le_of_le_one_right (norm_nonneg _) (by rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hx)).trans ((vision hp h.1 h0 he).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (QCD.Pearl.cap_base h) _) (beta_pos ..)) (norm_nonneg _)))
lemma dwarf (L:recordL)(hp:steady L k)(ht:0 ≤ t)(p:Momentum)(h:p∈baseCube)(ha:r≤ ‖p‖)(he:0<r): ‖stunted t L p‖ ≤ betaL L k * Real.pi ^ k/r*Real.exp (-t*r^2):=by
    have hm:=he.trans_le ha; have hu: p≠0 :=norm_pos_iff.mp hm
    unfold stunted; rw [norm_mul,Complex.norm_exp, axle_w h.1];
    have hv : ‖crewG L p‖ ≤ betaL L k * Real.pi ^ k/r := (vision hp h.1 hu (mem_ball_self (mul_pos ans hm))).trans (by gcongr; first | exact mul_nonneg (beta_pos ..) (by positivity); exact beta_pos ..; exact QCD.Pearl.cap_base h)
    apply mul_le_mul hv _ (by positivity) ((norm_nonneg _).trans hv); rw [← Complex.ofReal_neg,← Complex.ofReal_mul,Complex.ofReal_re]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left ((pow_le_pow_left₀ he.le ha _).trans (QCD.Pearl.vector_max p)) (neg_nonpos.mpr ht)
lemma coma (L:recordL)(p:Momentum)(h:physical p)(ht:0≤t): ‖crewG L p-stunted t L p‖≤ ‖crewG L p‖*t*(4*‖p‖^2):=by
    have he:= norm4 p
    unfold stunted; rw [show ∀ a b:ℂ,a-a*b=a*(1-b) from fun a b=>by ring, norm_mul, mul_assoc _ t, axle_w h,← Complex.ofReal_neg, ←Complex.ofReal_mul, ← Complex.ofReal_exp,← Complex.ofReal_one,← Complex.ofReal_sub, Complex.norm_real]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hx: 0≤lengthSq p:= (sq_nonneg _).trans (QCD.Pearl.vector_max p)
    have hq : Real.exp (-t * lengthSq p) ≤ 1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hx)
    rw [Real.norm_of_nonneg (sub_nonneg.mpr hq)]; exact le_trans (by linarith [Real.add_one_le_exp (-t * lengthSq p)]) (mul_le_mul_of_nonneg_left (show lengthSq p ≤ _ from he) ht)
@[simp] lemma zero_f (L:recordL) (t:ℝ): crewG L 0=0 ∧ stunted t L 0=0:= by simp [stunted,crewG,field]
end YM.Bank.Bee
#print axioms YM.Bank.Bee.vision
#print axioms YM.Bank.Bee.coma
