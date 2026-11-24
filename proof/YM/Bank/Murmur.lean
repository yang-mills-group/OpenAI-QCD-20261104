import YM.Bank.Bee
import YM.Maxwell.PotentialKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Murmur
open Function Lattice Laurent Bloch Metric RG Precision Filter Finset Next.Free Bee Pilot Pap
open MeasureTheory Analysis GaussianFourier
open Complex (I)
open scoped Topology BigOperators ENNReal ContDiff Matrix.Norms.L2Operator ComplexConjugate InnerProductSpace
variable {p:Momentum}{x y:E4}{r b t:ℝ}
local notation "π"=>Real.pi
def sound (x y:E4):ℂ:= Complex.exp (I*(inner ℝ x y))
lemma sounded (x y:E4): ‖sound x y‖=1:=by simp [sound,Complex.norm_exp]
def buzz (t:ℝ)(y:E4): ℝ:=Real.exp (-t*‖y‖^2)
abbrev vat (t:ℝ):=volume.restrict (Set.Ioi t)
def hρ (t:ℝ)(x:E4):ℝ:= (π/t)^2*Real.exp (-‖x‖^2/(4*t))
lemma chirped (ht:0<t) (x:E4): Integrable (fun y:E4=> sound x y*(buzz t y:ℂ)) ∧ ∫ y:E4,sound x y*(buzz t y:ℂ)=(hρ t x:ℂ):=by
   have hp: ∀ y:E4,sound x y*(buzz t y:ℂ)=Complex.exp (-(t:ℂ)*(↑‖y‖:ℂ)^2+I*(inner ℝ x y)):=by
       intro y; unfold sound buzz; push_cast; rw [← Complex.exp_add,add_comm]
   simp_rw [hp]; have he:0 < (t:ℂ).re:= ht
   refine ⟨integrable_cexp_neg_mul_sq_norm_add he I _,?_⟩
   rw [integral_cexp_neg_mul_sq_norm_add he I x,show ((Module.finrank ℝ E4:ℂ)/2)=((2:ℕ):ℂ) from ?_,Complex.cpow_natCast]
   · unfold hρ; push_cast; simp [Complex.I_sq]
   simp[E4,Axis]; ring
lemma buzz_i (ht:0<t):Integrable (buzz t):= ((chirped ht 0).1.norm).congr (Eventually.of_forall fun x=>by simp only [norm_mul,sounded,one_mul,Complex.norm_real]; exact Real.norm_of_nonneg (Real.exp_pos _).le)
lemma buzz_int (ht:0<t): ∫ y,buzz t y=(π/t)^2:=by
    have hv:= (chirped ht 0).2; simp only [sound,inner_zero_left,Complex.ofReal_zero, mul_zero,Complex.exp_zero,one_mul] at hv; rw [integral_complex_ofReal] at hv; apply (Complex.ofReal_inj.mp hv).trans; simp [hρ] -- name?

-- one dimension heat mass
lemma draining (ht:0<t) : Integrable (fun s:ℝ=> (π/s)^2) (vat t):=by
    have h := integrableOn_Ioi_rpow_of_lt (show (-2:ℝ)< -1 by norm_num) ht
    apply (h.const_mul (π^2)).congr; apply (ae_restrict_mem (μ:=volume) measurableSet_Ioi).mono; intro x hx; have he:0 < x:=lt_trans ht hx; dsimp only; rw [div_pow,div_eq_mul_inv,Real.rpow_neg he.le,Real.rpow_two] -- -2 parsed
lemma song {x:E4} (hx:x≠0)(ht:0<t): Integrable (fun s:ℝ=> hρ s x) (vat t)∧ ∫ s in Set.Ioi t,hρ s x= π^2*(4 /‖x‖^2)*(1-Real.exp (-‖x‖^2/(4*t))) :=by
   let g:= ‖x‖^2; have hg:0<g:=pow_pos (norm_pos_iff.mpr hx) 2; let k:= π^2*(4/g); let F(s:ℝ):= k*Real.exp (-g/(4*s))
   have he s (hs:s∈ Set.Ici t):HasDerivAt F (hρ s x) s :=by
       have hl:0<s:= lt_of_lt_of_le ht hs
       have hi:= ((((hasDerivAt_const s (-g)).div ((hasDerivAt_id' s).const_mul 4) (show 4*s≠0 from mul_ne_zero (by norm_num) hl.ne')).exp).const_mul k); convert hi using 1 <;> try rfl
       unfold hρ k g; have hb:=norm_pos_iff.mpr hx; simp only [Pi.div_apply]; field_simp; ring -- try
   have ha : Tendsto F atTop (𝓝 k):=by
       have hy:Tendsto (fun s:ℝ=> -g/(4*s)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
       simpa only [F,comp_apply,Real.exp_zero,mul_one] using (((Real.continuous_exp.tendsto _).comp hy).const_mul k)
   have hP s (hs:s∈Set.Ioi t):0 ≤ hρ s x:=by unfold hρ; positivity
   exact ⟨integrableOn_Ioi_deriv_of_nonneg' he hP ha,(integral_Ioi_of_hasDerivAt_of_nonneg' he hP ha).trans (by change k-_ = k*_; unfold F g; ring)⟩ -- name
lemma sugar (y:E4)(hy:y≠0)(t:ℝ): ∫ s in Set.Ioi t,buzz s y= buzz t y/‖y‖^2:=by
   let q:= ‖y‖^2; have hq:0<q:=pow_pos (norm_pos_iff.mpr hy) 2; let F(s:ℝ):= -(buzz s y/q)
   have hu s (hs:s∈Set.Ici t): HasDerivAt F (buzz s y) s:=by
       have hh := ((((hasDerivAt_id' s).neg.mul_const q).exp.div_const q).neg); convert hh using 1 <;> try rfl
       unfold buzz q; simp only [Pi.neg_apply]; have he:=norm_pos_iff.mpr hy; field_simp
   have hp: Tendsto F atTop (𝓝 0):=by
       have hf : Tendsto (fun s:ℝ=>Real.exp (-(s*q))) atTop (𝓝 0):= Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hq)
       simp only [← neg_mul] at hf; simpa only [F,buzz,q,zero_div,neg_zero] using (hf.div_const q).neg
   exact (integral_Ioi_of_hasDerivAt_of_nonneg' hu (fun i _=> (Real.exp_pos _).le) hp).trans (by rw [zero_sub]; unfold F; rw [neg_neg])
def χ (t:ℝ)(y:E4):ℝ:= buzz t y/‖y‖^2
def bandK (t:ℝ)(x:E4): E4→ℂ:=fun y=> sound x y*(χ t y:ℂ)
def normer := (2*π)⁻¹^4
def hired (t:ℝ)(x:E4):ℝ:= Maxwell.Green x*(1- Real.exp (-‖x‖^2/(4*t)))
lemma tuned (ht:0<t)(x:E4): Integrable (bandK t x) ∧ (x≠0→ (∫ y,bandK t x y) * (normer:ℂ)=(hired t x:ℂ)):=by
   let f(p:ℝ× E4):=sound x p.2*(buzz p.1 p.2:ℂ)
   have he : Integrable f ((vat t).prod volume):=by
       refine (integrable_prod_iff (show Continuous f by unfold f sound buzz; fun_prop).aestronglyMeasurable).2 ⟨?_,?_⟩
       · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with s hs; exact (chirped (t:=s) (lt_trans ht hs) x).1
       apply (draining ht).congr; filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with s hs; unfold f; simp_rw [norm_mul,sounded,one_mul,Complex.norm_real,show ∀ i:E4, ‖buzz s i‖=buzz s i from fun i=>Real.norm_of_nonneg (Real.exp_pos _).le] -- syntax
       exact (buzz_int (lt_trans ht hs)).symm
   have hB : (fun y=> ∫ s,f (s,y) ∂vat t) =ᵐ[volume] bandK t x:= by
       filter_upwards [show ∀ᵐ x:E4,x≠0 from (compl_mem_ae_iff.mpr (measure_singleton _))] with y hy
       dsimp only [f]; rw [integral_const_mul,integral_complex_ofReal]; change _ * (↑(∫ s in Set.Ioi t,buzz s y):ℂ)=_; rw [sugar y hy]; rfl
   refine ⟨he.integral_prod_right.congr hB,fun hx=>?_⟩ -- name?
   rw [← integral_congr_ae hB, ← MeasureTheory.integral_prod_symm f he, MeasureTheory.integral_prod f he]
   rw [integral_congr_ae (show (fun s:ℝ=>∫ y,f (s,y)) =ᵐ[vat t] fun s=> (↑(hρ s x):ℂ) from (ae_restrict_mem (μ:=volume) measurableSet_Ioi).mono fun s hs=> (chirped (lt_trans ht hs) x).2),integral_complex_ofReal]; unfold vat; rw [(song hx ht).2]; unfold hired normer; rw [Maxwell.normalization]; have hp:=Real.pi_pos; norm_cast; ring_nf; field_simp -- edit
end YM.Bank.Murmur
#print axioms YM.Bank.Murmur.tuned
