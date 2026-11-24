import YM.QCD.Creek.Wake

/-! # analysis independent reweights with given degree/geometric bills
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Function Finset Grass NormedSpace
open scoped Topology BigOperators ContDiff Classical
variable {I : Type*}{A B M: Type*} [Fintype A][Fintype B][Fintype M]
variable (f:A→ℝ) (hf:∀ i,0<f i)
def wscale (x : Alg A) : Alg A:= changeVars (Matrix.diagonal (fun a=>(f a:ℂ))) x
@[fun_prop] lemma wscale_continuous : Continuous (wscale f):= (changeVars _).toLinearMap.continuous_of_finiteDimensional
lemma wscale_mono (i:Finset A) : wscale f (mono i)=(∏ j∈i, (f j:ℂ)) • mono i:=by
  induction i using Finset.induction_on with
  | empty=> simp [wscale]
  | insert j s hj ih=>
    have he : Disjoint {j} s:= by simp [hj]
    have h := mono_mul_sign _ _ he; rw [disjUnion_eq_union,singleton_union,mono_single] at h
    let X:= changeVars (Matrix.diagonal (fun a=>(f a:ℂ)))
    have ht : wscale f (atom j*mono s)=(∏ k∈ insert j s, (f k:ℂ)) • (atom j*mono s):=by
      unfold wscale at *; rw [map_mul,change_atom,prod_insert hj,ih]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq, mul_smul_comm,smul_mul_assoc]; rw [smul_smul,mul_comm]
    obtain h|h:=h; · rwa [h] at ht
    rw [h] at ht; change X (mono _) = _; apply neg_injective; change X (-mono _) = _ at ht; rw [map_neg,smul_neg] at ht; exact ht

lemma wax (x : Alg A): wscale f x= ∑ s, coef s x • ((∏ i∈s,(f i:ℂ)) • mono s):=by
  conv_lhs=> rw [← write x]; unfold wscale; rw [map_sum]
  exact sum_congr rfl fun i _=> (map_smul _ _ _ |>.trans (congr_arg (coef i x • ·) (wscale_mono f i)))
def load (x:Alg A):ℝ:= ‖wscale f x‖
@[fun_prop] lemma payload : Continuous (load f) := (wscale_continuous f).norm
lemma load_nn (x) : 0 ≤ load f x:= norm_nonneg _
lemma load_scale (x:Alg A) (c:ℂ): load f (c • x)=‖c‖*load f x:=by unfold load wscale; rw [map_smul,norm_smul]
lemma load_sum (x:Finset I)(F:I→Alg A): load f (∑ i∈x,F i)≤∑ i∈x,load f (F i):=by unfold load wscale; rw [map_sum]; exact norm_sum_le ..
lemma load_mul (x y:Alg A): load f (x*y)≤load f x*load f y:=by unfold load wscale; rw [map_mul]; exact norm_mul_le _ _
include hf
lemma dry (x:Alg A): load f x=∑ s,(∏ i∈s, f i)*‖coef s x‖:=by
  rw [load, norm_def]; refine sum_congr rfl fun i _=>?_ ; rw [wax,map_sum,sum_eq_single i]
  · rw [map_smul,map_smul,Grass.read,smul_eq_mul,smul_eq_mul,mul_one,norm_mul,norm_prod]; rw [mul_comm]; congr 1; exact prod_congr rfl fun i _=> (Complex.norm_real _).trans (Real.norm_of_nonneg (hf i).le)
  · intro j _ hj; rw [map_smul,map_smul,read_other _ _ (Ne.symm hj),smul_zero,smul_zero]
  simp
lemma load_atom (i:A):load f (atom i)=f i:=by
  rw [← mono_single,load,wscale_mono, norm_smul,norm_mono, mul_one, prod_singleton,Complex.norm_real,Real.norm_of_nonneg (hf i).le]
lemma fee (i:A) : ∀ x, load f (v i x) ≤ (f i)⁻¹*load f x:=by
  intro x; have hx (s:Finset A) : load f (vary i (mono s)) ≤ (f i)⁻¹*load f (mono s):=by
    have ht (z : List A) (h:i∉ z): vary i (z.map atom).prod=0:=by
      induction z with
      | nil=> simp [vary_one]
      | cons k L ih=> simp only [List.mem_cons,not_or] at h; simp only [List.map_cons,List.prod_cons,vary_mul, vary_off _ _ h.1, ih h.2,mul_zero,zero_mul,add_zero]
    have hm (s: Finset A)(h:i∉s): vary i (mono s)=0:=by
      obtain ⟨u,-,hp,H⟩:= expression s; have hg:i∉List.ofFn u:=by simpa [(hp i)] using h
      rw [H]; simpa only [List.map_ofFn] using ht _ hg
    by_cases hj : i ∈ s
    · let t:=s.erase i; have hp:i∉t:=by simp[t]
      have hh : Disjoint {i} t:=by simp [hp]
      have he:=mono_mul_sign _ _ hh; rw [disjUnion_eq_union, singleton_union, mono_single,show insert i t=s from insert_erase hj] at he
      have hb: vary i (atom i*mono t)=mono t:=by rw [vary_mul,vary_self,hm t hp,mul_zero,one_mul, add_zero]
      have hy : load f (mono s)= f i*load f (mono t):=by unfold load; rw [wscale_mono,wscale_mono, norm_smul,norm_mono,norm_smul,norm_mono, show ∏ i∈ s,(f i:ℂ)= (f i:ℂ)*∏ j∈t,(f j:ℂ) by conv_lhs=> rw [← show insert i t=s from insert_erase hj,prod_insert hp]]; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hf i).le]; simp
      rw [hy,inv_mul_cancel_left₀ (hf i).ne']; rcases he with he|he <;> rw [he] at hb
      · rw [hb]
      rw [map_neg] at hb; unfold load wscale; simp [← hb] -- risky mono t recursive
    rw [hm s hj,load,wscale,map_zero,norm_zero]; exact mul_nonneg (inv_pos.mpr (hf i)).le (load_nn ..)
  change load f (vary i x) ≤ _; conv_lhs=> rw [← write x,map_sum]; simp only [map_smul]
  apply (load_sum ..).trans; rw [dry f hf,Finset.mul_sum]; refine sum_le_sum fun j _=> ?_ ; rw [load_scale]; have he: load f (mono j)=∏ i∈j,f i:=by unfold load; rw [wscale_mono,norm_smul,norm_mono,mul_one,norm_prod]; exact prod_congr rfl fun i _=> (Complex.norm_real _).trans (Real.norm_of_nonneg (hf i).le)
  apply (mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)).trans; rw [he]; exact le_of_eq (by ring)
end YM.QCD.Creek
