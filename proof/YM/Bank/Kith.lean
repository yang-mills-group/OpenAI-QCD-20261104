import YM.Bank.Murmur
import YM.Bank.Work
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Kith
open Function Lattice Laurent Bloch Metric RG Precision Filter Finset Next.Free Bee Pilot Pap Analysis
open Jump Zoom Murmur MeasureTheory
open Complex (I)
open scoped Topology BigOperators ENNReal InnerProductSpace ContDiff ComplexConjugate Matrix.Norms.L2Operator
variable {p:Momentum} {x y:E4}{r s t:ℝ}
def fly (p:E4) : Momentum:=fun i=> (p i:ℂ)
def rock (z: Cover):E4:= WithLp.toLp 2 fun i=> (z i:ℝ)
lemma scope_p (p:E4): physical (fly p):= (physical_iff _).mpr fun _=>rfl
lemma size_p (p:E4): earth (fly p) = p:=by ext i; rfl
lemma trim_p (p:Momentum) (h:physical p): fly (earth p) = p:=funext (inland h)
lemma born_p : Continuous fly:=continuous_pi fun i=>by unfold fly; fun_prop
lemma axle_p (x:E4): axle (fly x)=((‖x‖^2:ℝ):ℂ):=by rw [axle_w (scope_p x),EuclideanSpace.norm_sq_eq]; simp [lengthSq,fly]
lemma blown (t:ℝ)(p:E4): Complex.exp (-(t:ℂ)*axle (fly p))=(buzz t p:ℂ):=by rw [axle_p]; unfold buzz; push_cast; rfl
lemma hits_e (s: Cover)(x:E4): sound (rock s) x=mode (fly x) s:=by unfold sound mode; congr 2; simp only [rock,PiLp.inner_apply,RCLike.inner_apply]; rw [Complex.ofReal_sum]; apply sum_congr rfl; intro i _; simp [fly]
lemma hike (w:ℝ) (p:E4):0 ≤ χ w p:= div_nonneg (Real.exp_pos _).le (by positivity)
lemma costs_i (ht:0<t):Integrable (χ t) :=by apply (tuned ht 0).1.norm.congr; filter_upwards [] with i; simp only [bandK,norm_mul,sounded,one_mul,Complex.norm_real]; exact Real.norm_of_nonneg (hike t i)
lemma ample (ht:0<t)(k:ℕ) : Integrable (fun p:E4=> χ t p*‖p‖^k):=by
   let z:= t/2; have hz:0<z:=half_pos ht
   let g(p:ℝ) := p^k * Real.exp (-z*p^2)
   have hh: Tendsto g atTop (𝓝 0):=by
       have he:=tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) z hz; simp only [Real.rpow_natCast] at he
       refine squeeze_zero' ?_ ?_ he
       · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; unfold g; positivity
       filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx; dsimp[g]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by nlinarith) (by linarith))) (pow_nonneg (by linarith) _)
   obtain ⟨A,hA⟩:= eventually_atTop.mp (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
   obtain ⟨C,hC⟩:= (isCompact_Icc (α:=ℝ) (a:=0) (b:=A)).bddAbove_image (show Continuous g by unfold g; fun_prop).continuousOn
   let C':=max C 1
   refine ((costs_i hz).mul_const C').mono' (by unfold χ buzz; fun_prop) (Eventually.of_forall fun i=>?_)
   rw [Real.norm_of_nonneg (mul_nonneg (hike ..) (by positivity))]
   have hx : χ t i*‖i‖^k=χ z i * g ‖i‖:=by unfold g χ buzz; rw [show -t*‖i‖^2=-z*‖i‖^2+-z*‖i‖^2 by unfold z; ring, Real.exp_add]; ring
   rw [hx]; apply mul_le_mul_of_nonneg_left _ (hike ..); rcases le_total ‖i‖ A with he|he
   · exact (hC (Set.mem_image_of_mem g (show ‖i‖∈Set.Icc 0 A from ⟨norm_nonneg _,he⟩))).trans (le_max_left ..)
   exact (show g _ < 1 from hA _ he).le.trans (le_max_right ..)
lemma tariff (p:E4)(l:List Axis) : ‖Wale.barrier (fly p) l‖ ≤ ‖p‖^l.length:= (Bee.listed ..).trans (pow_le_pow_left₀ (norm_nonneg _) ((inch (scope_p p)).trans_eq (by rw [size_p])) _)
lemma curtain (r:List Axis): Continuous (fun v=>Wale.barrier v r):=continuous_iff_continuousAt.mpr fun x=> (foil r x).continuousAt

def shine (t:ℝ)(l:List Axis)(x p:E4):= sound x p*(χ t p:ℂ)*Wale.barrier (fly p) l
lemma shore (ht:0<t)(l:List Axis)(x:E4):Integrable (shine t l x):=by
   refine (ample ht l.length).mono' ?_ (Eventually.of_forall fun y=> ?_)
   · unfold shine; exact (((show Continuous (sound x) by unfold sound; fun_prop).aestronglyMeasurable.mul (show Measurable (fun p:E4=> (χ t p:ℂ)) from Complex.continuous_ofReal.measurable.comp (by unfold χ buzz; fun_prop)).aestronglyMeasurable).mul ((curtain l).comp born_p).aestronglyMeasurable)
   unfold shine; rw [norm_mul,norm_mul,sounded,one_mul,Complex.norm_real,Real.norm_of_nonneg (hike ..)]; exact mul_le_mul_of_nonneg_left (tariff ..) (hike ..)

def view (r:ℝ)(l:List Axis)(p:E4):= normer • ∫ x,shine r l p x
-- CLM derivative kernel

def tim (p:E4): E4→L[ℝ] ℂ:= I • Complex.ofRealCLM.comp ((innerSL ℝ).flip p)
lemma soundF (p y:E4):HasFDerivAt (fun x=> sound x p) (sound y p • tim p) y:= (tim p).hasFDerivAt.cexp
lemma timeG (p x:E4) : tim p x=I*(↑(inner ℝ x p):ℂ):=rfl
lemma costT (p:E4): ‖tim p‖≤‖p‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro x; rw [timeG, norm_mul,Complex.norm_I,Complex.norm_real,one_mul]; exact (norm_inner_le_norm x p).trans_eq (by ring)
lemma tim_m : Continuous tim:=by
    unfold tim; fun_prop
lemma reading (ht:0<t)(p:E4)(i:Axis)(l:List Axis): DifferentiableAt ℝ (view t l) p ∧ Analysis.D (basis i) (view t l) p=view t (i::l) p:=by
    let f:=shine t l; let X(p x:E4):= f p x • tim x
    let b(x:E4):= χ t x*‖x‖^(l.length+1)
    have hm x : ∀ y, HasFDerivAt (fun w=> f w x) (X y x) y:=by
        intro y; unfold X f shine; convert ((soundF x y).mul_const (χ t x:ℂ)).mul_const (Wale.barrier (fly x) l) using 1 <;>try rfl
        ext1 y; simp; ring
    have hx (p x:E4):‖X p x‖≤b x:=by
        unfold X f shine; rw [norm_smul,norm_mul,norm_mul,sounded,one_mul,Complex.norm_real,Real.norm_of_nonneg (hike ..)]; apply (mul_le_mul (mul_le_mul_of_nonneg_left (tariff ..) (hike ..)) (costT _) (norm_nonneg _) (mul_nonneg (hike ..) (pow_nonneg (norm_nonneg _) _))).trans_eq; unfold b; ring
    have hh : Integrable (X p) :=by apply (ample ht (l.length+1)).mono'; exact (shore ht l p).1.smul tim_m.aestronglyMeasurable; exact Eventually.of_forall (hx p)
    have he:HasFDerivAt (view t l) (normer • ∫ x,X p x) p:= by
         exact HasFDerivAt.const_smul (hasFDerivAt_integral_of_dominated_of_fderiv_le (s:=Set.univ) univ_mem (Eventually.of_forall fun p=>(shore ht l p).1) (shore ht l p) hh.1 (Eventually.of_forall fun x p _=>hx p x) (ample ht (l.length+1)) (Eventually.of_forall fun x p _ => hm x p)) normer
    refine ⟨he.differentiableAt,?_⟩; rw [Analysis.D,he.fderiv,ContinuousLinearMap.smul_apply,ContinuousLinearMap.integral_apply hh]; congr 1; -- view unfold
    refine integral_congr_ae (Eventually.of_forall fun x=>?_); unfold X f shine; dsimp only; rw [ContinuousLinearMap.smul_apply,timeG,basis_inner]; change _*_= (_*_* ((I* _)*Wale.barrier (fly x) l)); unfold fly; ring
lemma blank (x:E4): x≠0→0<t→view t [] x=(hired t x:ℂ):=by
   intro hx ht; rw [view,←(tuned ht x).2 hx]; simp [shine,Wale.barrier,bandK,Complex.real_smul,mul_comm]

def earn (l: List Axis)(f:E4→ℂ):= l.foldr (fun i F=> Analysis.D (basis i) F) f
lemma nebula (l: List Axis)(x:E4) (hp:x≠0) (ht:0<t):view t l x=earn l (fun i=> (hired t i:ℂ)) x:=by
    induction l generalizing x with
    | nil=> exact blank x hp ht
    | cons a l ih=> rw [←(reading ht x a l).2]; exact Analysis.GermD _ (Eventually.mono (Maxwell.open_away.mem_nhds hp) fun y hy => ih y hy)
end YM.Bank.Kith
#print axioms YM.Bank.Kith.nebula
