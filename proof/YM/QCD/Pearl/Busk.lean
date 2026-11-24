import YM.QCD.Pearl.Swan

/-! # polynomials and symmetric remainders, use real euclidean radius -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para Pinch
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
abbrev ReP:= Axis→ℝ
def castP (k:ReP): Momentum:=fun i=> (k i:ℂ)
def boost (u:ℝ)(i:Axis):Momentum:=(u:ℂ) • step i
lemma liftV (k:ReP)(x:ℝ)(i:Axis):castP k+boost x i=castP (k+x • step i):=by ext1 j; by_cases h:j=i <;> simp [castP,boost,h]
lemma skyZ (k:ReP): sky (castP k) = (lensq k:ℂ):=by simp [sky,castP,lensq]
lemma arcP (p:ReP): physical (castP p):= by ext; simp[castP]
lemma crescent (k:ReP)(t:ℝ)(a:Axis): lensq (k+t • step a)=lensq k+2*k a*t+t^2:=by
  unfold lensq; simp_rw [Pi.add_apply, Pi.smul_apply,smul_eq_mul, add_pow_two,sum_add_distrib]; simp [step_apply,mul_ite,ite_pow]
lemma tangentP (k:ReP)(t:ℝ)(a:Axis): (∑ i:Axis,(k i:ℂ)*castP (k+t • step a) i)= (lensq k:ℂ)+(k a:ℂ)* (t:ℂ):=by
  unfold castP lensq; push_cast; simp only [Pi.add_apply,Complex.ofReal_add,Pi.smul_apply,smul_eq_mul,mul_add,sum_add_distrib]; congr 1; · simp only [sq]
  simp [step_apply,mul_ite,apply_ite]
def trekS (C:su.Color)(k:ReP)(a:Axis)(t:ℝ):ℝ:= (crown (touch (echo C)*wave (gamma 1)) (boost t a) (castP k)).re
def hopC (k:ReP)(a:Axis):=if a=(1:Axis) then k 1 else -(k a)
def capital (k:ReP):=2*(k 1)^2-lensq k
lemma shipS (C:su.Color)(hC:‖C‖=1)(k:ReP)(a:Axis)(t:ℝ): trekS C k a t=12*(capital k+hopC k a*t)/(lensq k*(lensq k+2*k a*t+t^2)):=by
  unfold trekS; rw [glimmer _ _ _ _ hC,liftV,skyZ,skyZ,crescent];
  rw [show (∑ i,castP k i* castP (k+t • step a) i)= _ from tangentP k t a];
  refine congr_arg Complex.re ?_ |>.trans (Complex.ofReal_re _)
  unfold capital hopC castP; split; next he=> subst a; simp; ring
  next ht=> simp [Ne.symm ht]; ring

def f0 (k:ReP) (a:Axis) :ℝ:=12*(capital k*((2*k a)^2-lensq k)-hopC k a*(2*k a)*lensq k)/(lensq k)^4
lemma ordinate (k:ReP)(i:Axis): (k i)^2≤lensq k:=single_le_sum (fun j _=>sq_nonneg (k j)) (mem_univ i)
def fry (k:ReP):=Real.sqrt (lensq k)
lemma fry_nn (k:ReP): 0≤ fry k:=Real.sqrt_nonneg _
lemma fry_sq (k:ReP): fry k^2=lensq k:=Real.sq_sqrt (lensq_ge _)
lemma fry_sub (k:ReP)(i:Axis): |k i|≤ fry k:=by apply le_of_sq_le_sq _ (fry_nn k); rw [sq_abs,fry_sq]; exact ordinate k i
lemma fry_lower (k:ReP): ‖castP k‖≤fry k:= by refine (pi_norm_le_iff_of_nonneg (fry_nn k)).mpr fun i=>?_ ; simpa only [castP,Complex.norm_real] using! fry_sub k i
lemma fry_upper (k:ReP): fry k ≤ 2*‖castP k‖:=by
  apply le_of_sq_le_sq _ (by positivity); rw [fry_sq]; unfold lensq
  have he i: (k i)^2≤‖castP k‖^2:=by rw [← sq_abs]; apply pow_le_pow_left₀ (abs_nonneg _) (by simpa only [castP,Complex.norm_real] using! norm_le_pi_norm (castP k) i)
  exact (sum_le_sum fun i _=> he i).trans_eq (by simp [Axis]; ring)
-- package rest scalar rational. A=R^2 a0 ; D=R d0 ; x=k_a/R y=t/R
lemma rational_bill {x a d t:ℝ} (ha:|a|≤1)(hx:|x|≤1)(hd:|d|≤1)(ht:|t|≤1/4) :
    |(a+d*t)/(1+2*x*t+t^2) - (a+(d-2*x*a)*t +(a*(4*x^2-1)-2*x*d)*t^2)|≤40*|t|^3:=by
  let b:=d-2*x*a; let c:=a*(4*x^2-1)-2*x*d
  have h1 : |2*x*t|≤ 2*|t|:=by simp only [abs_mul]; gcongr; exact mul_le_of_le_one_right (abs_nonneg _) hx |>.trans_eq (by norm_num)
  have h2: (1:ℝ)/2≤1+2*x*t+t^2:=by linarith [(abs_le.mp h1).1, sq_nonneg t]
  have hp : 0<1+2*x*t+t^2:=by linarith
  have hb:|b|≤3:=by unfold b; apply (abs_sub ..).trans; refine (add_le_add hd ?_).trans_eq (by norm_num : (1:ℝ)+2=3); rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; exact (mul_le_of_le_one_right (by positivity) ha).trans (mul_le_of_le_one_right (by norm_num) hx)
  have hc: |c|≤5:=by
    have h: |4*x^2-1|≤3:=by have he:= mul_self_le_mul_self (abs_nonneg x) hx; simp only [← sq, sq_abs] at he; apply abs_le.mpr; constructor <;> nlinarith
    unfold c; apply (abs_sub ..).trans
    refine (add_le_add (show |a*(4*x^2-1)|≤3 from ?_) (show |2*x*d|≤2 from ?_)).trans_eq (by norm_num)
    · rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) ha).trans h
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (mul_le_of_le_one_right (by positivity) hd).trans (mul_le_of_le_one_right (by positivity) hx)
  let R:= (1+2*x*t+t^2); have he: 0<R:=hp
  have hX:= (calc
    |c*t+(2*x*c+b)| ≤ 2+(2*1*5+3):= by
      refine (abs_add_le ..).trans (add_le_add ?_ ((abs_add_le ..).trans (add_le_add ?_ hb)))
      · rw [abs_mul]; exact (mul_le_mul hc ht (abs_nonneg _) (by norm_num)).trans (by norm_num)
      rw [abs_mul,abs_mul]; norm_num; calc
        _ ≤ 2*1*5:= mul_le_mul (mul_le_mul_of_nonneg_left hx (by positivity)) hc (by positivity) (by positivity)
        _ = 10:= by norm_num
    _ ≤ 40*R := by unfold R; linarith)
  change |_/R-(a+b*t+c*t^2)|≤ _; rw [div_sub' he.ne',abs_div, abs_of_pos he,div_le_iff₀ he]
  rw [show a+d*t-R*(a+b*t+c*t^2)= -(c*t+(2*x*c+b))*t^3 from ?_,abs_mul, abs_neg,abs_pow]; exact (mul_le_mul_of_nonneg_right hX (by positivity : 0≤|t|^3)).trans_eq (by ring)
  unfold b c R; ring
end YM.QCD.Pearl
