import YM.QCD.Creek.Cost
import YM.QCD.Creek.Bark

/-! # per-dollar costs including the discarded-first exponential
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek.Ledge
open Finset Filter Function NormedSpace Grass
open scoped BigOperators Topology ContDiff Classical Matrix
variable {ι A B M: Type*}[Fintype A][Fintype B][Fintype M]
variable {D F: EndA A}{f:A→ℝ}{p q:ℝ}
structure Pledge (f:A→ℝ)(D:EndA A)(p:ℝ):Prop where
 nn : 0 ≤p
 rates x : load f (D x) ≤p*load f x
def excess (D: EndA A):= birth D-1
local instance {A:Type*}[Fintype A] : NormedAlgebra ℚ (EndA A):=.restrictScalars ℚ ℂ _
namespace Pledge
lemma bumps (H:Pledge f D p)(h:p≤q):Pledge f D q:=⟨H.nn.trans h,fun i=> (H.rates i).trans (mul_le_mul_of_nonneg_right h (load_nn _ _))⟩
lemma combines (H:Pledge f D p)(K:Pledge f F q): Pledge f (D*F) (p*q):=⟨mul_nonneg H.nn K.nn,fun x=> (H.rates _).trans ((mul_le_mul_of_nonneg_left (K.rates x) H.nn).trans_eq (by rw [← mul_assoc]))⟩
lemma powX (H:Pledge f D p)(k:ℕ):Pledge f (D^k) (p^k):=by
  induction k with
  | zero=> rw [pow_zero,pow_zero]; exact ⟨zero_le_one,fun _=>(one_mul _).symm.le⟩
  | succ k ih=>rw [pow_succ,pow_succ]; exact ih.combines H
lemma penny (x:ℂ)(H:Pledge f D p): Pledge f (x • D) (‖x‖*p):=by refine ⟨mul_nonneg (by positivity) H.nn,fun i=>?_⟩; change load f (x • D i)≤ _; rw [load_scale,mul_assoc]; exact mul_le_mul_of_nonneg_left (H.rates _) (by positivity)
lemma gathered {c:ι→ℝ} (S:Finset ι)(D:ι→EndA A)(h:∀ i∈S,Pledge f (D i) (c i)):Pledge f (∑ i∈S,D i) (∑ i∈ S,c i):=by
  refine ⟨sum_nonneg fun i hi=> (h i hi).nn,fun x=>?_⟩; rw [ContinuousLinearMap.sum_apply,sum_mul]; apply (load_sum f S _).trans; exact sum_le_sum fun i hi=> (h i hi).rates _
lemma surge (H:Pledge f D p): Pledge f (excess D) (Real.exp p-1):=by
  refine ⟨sub_nonneg.mpr (Real.one_le_exp H.nn),fun x=>?_⟩
  let t (n:ℕ):= ((n.factorial:ℂ)⁻¹) • D^n
  let g n := (n.factorial:ℝ)⁻¹*p^n
  have hh :HasSum t (birth D):=exp_series_hasSum_exp' D
  have hp :HasSum g (Real.exp p):=by
    have hv : HasSum (fun i:ℕ=> ((i.factorial:ℝ)⁻¹) • p^i) (NormedSpace.exp p):=exp_series_hasSum_exp' p
    rw [Real.exp_eq_exp_ℝ]; exact hv
  have he n: Pledge f (t n) (g n):= by
    unfold t g; have hk:= (powX H n).penny ((n.factorial:ℂ)⁻¹); simpa using hk
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show t 0=1 by simp [t]] at hh
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show g 0=1 by simp [g]] at hp
  let F n : Alg A:= t (n+1) x; let T:= fun (s : Finset ℕ)=>∑ i∈s,F i
  have hm : Tendsto T atTop (𝓝 (excess D x)):= (ContinuousLinearMap.apply ℂ (Alg A) x|>.hasSum hh)
  exact le_of_tendsto_of_tendsto' ((payload f).continuousAt.tendsto.comp hm) (show Tendsto (fun s : Finset ℕ=>∑ i∈s,g (i+1)*load f x) atTop _ from hp.mul_right (load f x))
    (fun s=> (load_sum f s F).trans (sum_le_sum fun i _=> (he (i+1)).rates x))
lemma twice (H:Pledge f D p)(hp:p≤1): Pledge f (excess D) (Real.exp 1*p):=by
  apply H.surge.bumps; have he:=Real.add_one_le_exp (-p); rw [Real.exp_neg] at he; have ht := mul_le_mul_of_nonneg_right he (Real.exp_pos p).le; rw [inv_mul_cancel₀ (Real.exp_ne_zero p)] at ht; nlinarith [mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) H.nn]

end Pledge

variable (S : Matrix A B ℂ)(K:Matrix A A ℂ)(z : M →ℝ) (hp:∀ i,0< z i)
lemma glacier (i:M) (hp:∀ i,0< z i): Pledge z (v i) ((z i)⁻¹):=⟨inv_nonneg.mpr (hp _).le, fee z hp i⟩
lemma wand (i:M) (hp:∀ i,0< z i): Pledge z (l i) (z i):=⟨(hp _).le,fun x=> (load_mul z (atom i) x).trans_eq (by rw [load_atom z hp i])⟩
include hp
def barksP (z:M→ℝ)(u:A↪M)(w:B↪M):=∑ i,∑ j,‖S i j‖*(z (w j)*(z (u i))⁻¹)
lemma prices (u:A↪M)(w:B↪M): Pledge z (barkG u w S) (barksP S z u w):=by
   apply Pledge.gathered; intro i _; apply Pledge.gathered; intro j _; exact Pledge.penny _ ((wand z (w j) hp).combines (glacier z (u i) hp))
def pawn (z:M→ℝ)(u:Pairs A↪M):=∑ i,∑ j,‖K i j‖*((z (met u j))⁻¹*(z (pet u i))⁻¹)
lemma parent (u:Pairs A↪M): Pledge z (pond u K) (pawn K z u):=by apply Pledge.gathered; intro i _; apply Pledge.gathered; intro j _; exact Pledge.penny _ ((glacier z (met u j) hp).combines (glacier z (pet u i) hp))
end YM.QCD.Creek.Ledge
