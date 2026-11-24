import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic

/-!
# Sample complex zeros at log cost proportional to their number

Discrete proof (so don't have to handle log singularities on a real interval,
continuation from a circle through real roots, or choosing a real almost-everywhere
radius). Costs intentionally not sharp.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Finset Set Function Polynomial
open scoped Topology BigOperators

def product (l : List ℂ) (x : ℂ) := (l.map (x-·)).prod

def expansion (l : List ℂ) (t : ℂ) : Polynomial ℂ := (l.map fun a => Polynomial.C t * Polynomial.X + Polynomial.C (1/2-a)).prod

lemma evaluate (l : List ℂ) (t x : ℂ) : (expansion l t).eval x = product l (1/2+t*x) := by
    induction l with
    | nil => simp [expansion, product]
    | cons a l ih =>
      simp only [expansion, List.map_cons, List.prod_cons,product,eval_mul, eval_add,eval_C,eval_X]
      unfold expansion product at ih; rw [ih]; ring

lemma coefficients (l : List ℂ) (t : ℂ) (h : t≠0) :
    (expansion l t).leadingCoeff = t^l.length ∧ (expansion l t).natDegree=l.length := by
    induction l with
    | nil => simp [expansion]
    | cons a l ih =>
      obtain ⟨ht,hp⟩:= ih
      let p := Polynomial.C t * Polynomial.X + Polynomial.C (1/2-a)
      have hx : p.natDegree=1:= by unfold p; rw [natDegree_add_C,natDegree_C_mul_X _ h]
      have hu : p.leadingCoeff=t:= by rw [leadingCoeff,hx]; simp [p]
      have hv : p≠0:= leadingCoeff_ne_zero.mp (hu.symm ▸ h)
      have he : expansion l t ≠ 0 := leadingCoeff_ne_zero.mp (ht.symm ▸ pow_ne_zero _ h)
      rw [show expansion (a::l) t = p*expansion l t from rfl]
      rw [Polynomial.natDegree_mul hv he, Polynomial.leadingCoeff_mul]
      rw [ht,hp,hu,hx]; simp [pow_succ',add_comm]

lemma factorial_bound (n : ℕ) : (n:ℝ)^n / Real.exp 1 ^ n ≤ (n.factorial:ℝ) := by
  have hp : 0 < (n.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_iff₀ (by positivity : 0 < Real.exp 1 ^ n)]
  rw [← Real.exp_nat_mul,mul_one, mul_comm (n.factorial:ℝ)]
  exact (div_le_iff₀ hp).mp (Real.pow_div_factorial_le_exp _ (by positivity) n)

lemma iterate_bound (g : ℂ → ℂ) (n : ℕ) (k : ℕ) (M : ℝ)
    (h : ∀ j ≤ n, ‖g ((k:ℂ)+j)‖ < M) : ‖(fwdDiff (1:ℂ))^[n] g k‖ < 2^n * M := by
  induction n generalizing k with
  | zero => simpa using h 0 (by omega)
  | succ n ih =>
    rw [iterate_succ_apply']; unfold fwdDiff
    rw [← Nat.cast_add_one]
    apply lt_of_le_of_lt (norm_sub_le ..)
    have hp := ih k (fun j hj=> h j (by omega));
    have ht := ih (k+1) (fun j hj=> by specialize h (j+1) (by omega); push_cast at *; simpa only [add_right_comm,← add_assoc] using h)
    rw [pow_succ']; apply (add_lt_add ht hp).trans_le; linarith

/-- One λ in [1/2,1] suffices. -/
theorem some_real (l : List ℂ) : ∃ x ∈ Icc (1/2 : ℝ) 1,
     (4 * Real.exp 1)⁻¹ ^ l.length ≤ ‖product l x‖ := by
    by_cases h : l=[]
    · subst l; exact ⟨1,by norm_num,by simp [product]⟩
    let n:=l.length; have hp : n>0:=List.length_pos_iff.mpr h; have he : (0:ℝ)<n:=by exact_mod_cast hp
    let t:ℝ:=(2*(n:ℝ))⁻¹; have ht:0<t:=by unfold t; positivity
    let e:=Real.exp 1
    let M := ((4*e)⁻¹)^n
    let P:= expansion l t
    by_contra! hn
    have hu (x : ℕ) (hx : x≤n) : ‖P.eval ((0:ℕ)+ (x:ℂ))‖<M:=by
      rw [Nat.cast_zero,zero_add,show P=expansion l t from rfl,evaluate]
      let z:ℝ:=1/2+t*x; have hh : 0≤t*x:=by positivity
      rw [← show (z:ℂ)=1/2+(t:ℂ)*x from (by unfold z; push_cast; rfl)]
      apply hn z (show z∈ Set.Icc _ _ from ⟨by unfold z; linarith,by
        have hf : (x:ℝ)≤n:=by exact_mod_cast hx
        have hy : t*n≤1/2:=by unfold t; rw [inv_mul_eq_div]; field_simp; nlinarith
        unfold z; nlinarith ⟩)
    obtain ⟨hL,hP⟩ := coefficients l ↑t (Complex.ofReal_ne_zero.mpr ht.ne')
    change P.natDegree=n at hP
    have hv := iterate_bound P.eval n 0 M hu
    have hh : (fwdDiff (1:ℂ))^[n] P.eval 0=(t:ℂ)^n*(n.factorial:ℂ):=by
      have hW:= Polynomial.fwdDiff_iter_degree_eq_factorial P; rw [hP, show P.leadingCoeff= _ from hL] at hW; rw [hW]; rfl
    rw [Nat.cast_zero,hh,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht.le,Complex.norm_natCast] at hv
    refine (?_ : 2^n*M ≤ t^n * (n.factorial:ℝ)).not_gt hv
    have hd : (0:ℝ) < Real.exp 1^n:=by positivity
    calc
      _ = t^n * ((n:ℝ)^n / Real.exp 1 ^ n) := by unfold t M e; rw [← div_pow, ← mul_pow, ← mul_pow]; congr 1; field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_bound _) (by positivity)
end YM.Massive.Pressure
