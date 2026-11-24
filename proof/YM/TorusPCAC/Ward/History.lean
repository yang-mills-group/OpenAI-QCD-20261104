import YM.TorusPCAC.Ward.Transport
import YM.TorusPCAC.Finite.Evolution

/-!
# PCAC / V progress: one whole equation at level M

Total transmission lemma for the very actual trajectory. Includes the passage
on pointwise-integrated densities with all other marks (take arbitrary X
initially). The kernel is per actual `U` at every step. Actual `A`s are
off-diagonal flavor matrices, with no tracelessness requirement on spin (so
both pseudoscalar AND scalar probes). No projection to vacuum or flavor
singlets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Ward
open QCD QCD.Grass QCD.Lat QCD.Kit Lattice Wilson Finite Finset MeasureTheory Function RG
open scoped Matrix Topology BigOperators Kronecker
variable {c f n : Side} {N : ℕ}

/-- Internal inserted matrix including both choices `g5` and `1`. -/
structure Pair (N : ℕ) where
  l : Flavor N
  r : Flavor N
  neq : l ≠ r
  u : Spike

namespace Pair
variable (p : Pair N)
def flavor : Matrix (Flavor N) (Flavor N) ℂ := Matrix.of fun i j=> if i=p.l ∧ j=p.r then 1 else 0
lemma chargeFree (i : Flavor N) : p.flavor i i=0 := by
  simp only [flavor, Matrix.of_apply, ite_eq_right_iff,one_ne_zero,imp_false]; exact fun h=>p.neq (h.1.symm.trans h.2)
def symbol (n : Side) : MatS n N := onSpin n p.u ⊗ₖ p.flavor
lemma trace (n : Side) : Matrix.trace (p.symbol n)=0 := by simp only [symbol, Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag_apply, chargeFree,sum_const_zero, mul_zero]

/-- No momentum or link covariance assumption needed. -/
lemma neutral (W : Spike) (g : Matrix (Flavor N) (Flavor N) ℂ) (M : StepData c f) (U : Grid f) :
    meanSpin M U * (onSpin f W ⊗ₖ g)=(onSpin c W ⊗ₖ g) * meanSpin M U := by
  rw [show meanSpin M U= Flume.tied (prototype _) _ 0 U ⊗ₖ (1:Matrix (Flavor N) (Flavor N) ℂ) from (Matrix.kronecker_one _).symm]
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,one_mul,mul_one,Pine.tiedSpin]
lemma flies (s : Bool) (M : StepData c f) (U : Grid f) : st s (meanSpin M U)*alpha s (p.symbol f)=alpha s (p.symbol c)*st s (meanSpin M U):=by
  cases s
  · exact neutral p.u p.flavor M U
  · let Q := meanSpin (N:=N) M U
    change Qᴴᵀ * Matrix.transpose _=Matrix.transpose _ * Qᴴᵀ
    rw [← Matrix.transpose_mul,← Matrix.transpose_mul]; congr 1
    have he (n : Side) : (p.symbol n)ᴴ=onSpin n (star p.u) ⊗ₖ p.flavorᴴ := by unfold symbol; rw [Matrix.conjTranspose_kronecker, ← Matrix.star_eq_conjTranspose,on_spin_star]
    have hv : Q * (p.symbol f)ᴴ=(p.symbol c)ᴴ * Q := by rw [he,he]; exact neutral ..
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using congr_arg (·ᴴ) hv

/-- The **local** position equation at x. Acts on entire density. -/
def each (n : Side) (x : Site n) : MatS n N := Matrix.of fun i j => if i.1.1=x then p.symbol n i j else 0
lemma each_trace (n : Side) (x : Site n) : Matrix.trace (p.each n x)=0 :=by simp only [Matrix.trace,Matrix.diag_apply, each, Matrix.of_apply, symbol, Matrix.kroneckerMap_apply,chargeFree,mul_zero,ite_self,sum_const_zero] -- order

end Pair

/-- Actual section of equations, even when there is no kinetic gap at input.
Kernel can hold any insertions; the consequence after integration holds on it.
-/
def each (p : Pair N) (s : Bool) (x : Site n) (F : Density n N) : Density n N := fun U=>(rotation s (p.each n x)) (F U)
def global (p : Pair N) (s : Bool) (F : Density n N) : Density n N := fun U=> (rotation s (p.symbol n)) (F U)

lemma summed (p : Pair N) (s : Bool) (F : Density n N) : global p s F= ∑ x : Site n, each p s x F := by
  have hp (i j : Modes n N) : alpha s (p.symbol n) i j=∑ x : Site n, alpha s (p.each n x) i j:=by cases s <;> simp [Pair.each,alpha]
  ext1 U
  simp only [global, each, Finset.sum_apply,rotation,LinearMap.coe_mk,AddHom.coe_mk];
  simp_rw [hp,sum_smul]
  rw [sum_comm (s:=univ) (t:=univ) (f:=fun (x : Site n) (i : Modes n N)=> ∑ j,
    alpha s (p.each n x) i j • (letter s j * D s i (F U)))]
  exact sum_congr rfl fun i _ => sum_comm
lemma localized (p : Pair N) (s : Bool) (x : Site n) (F : Density n N) : Density.volume (each p s x F)=0 := by
  simp only [Density.volume, each, rotation_killed s (p.each_trace n x), MeasureTheory.integral_zero]
lemma integrated (p : Pair N) (s : Bool) (F : Density n N) : Density.volume (global p s F)=0:=by
  simp only [Density.volume, global, rotation_killed s (p.trace n), MeasureTheory.integral_zero]

lemma global_cont (p : Pair N) (s : Bool) {F : Density n N} (h : Continuous F) : Continuous (global p s F):=(rotation _ _).continuous_of_finiteDimensional.comp h
lemma each_cont (p : Pair N) (s : Bool) (x : Site n) {F : Density n N} (h : Continuous F) : Continuous (each p s x F):=(rotation _ _).continuous_of_finiteDimensional.comp h

variable (H : History N) (p : Pair N) (q M : ℕ)
namespace History

/-- from searching-window depth M. Give unused values above. -/
def haul (p : Pair N) (X : Density (H.lattice M q) N) (hX : Continuous X) (m : ℕ) : Pass (H.lattice m q) N :=
  if hR : m=M then by
    subst m
    exact ⟨X, fun _ _=> 0,hX,fun _ _=> continuous_const⟩
  else if _hg : m < M then Pass.onward (haul p X hX (m+1)) (H.step m q) (H.branches m)
    (H.beta q (m+1)) (H.w q m) (p.symbol _)
  else ⟨0,fun _ _=> 0,continuous_const,fun _ _=> continuous_const⟩
termination_by M-m

variable {q M} (X : Density (H.lattice M q) N) (hX : Continuous X) {m : ℕ}

lemma boundary : (haul H q M p X hX M).kernel=X ∧ ∀ i j, (haul H q M p X hX M).car i j=0 := by rw [haul, dif_pos rfl]; exact ⟨rfl,fun _ _=>rfl⟩
lemma haul_next (h : m<M) : haul H q M p X hX m=Pass.onward (haul H q M p X hX (m+1)) (H.step m q) (H.branches m) (H.beta q (m+1)) (H.w q m) (p.symbol _) := by rw [haul,dif_neg h.ne,dif_pos h]
lemma precise (h : m ≤ M) : (haul H q M p X hX m).kernel=H.push q m M X:=by
  induction h using Nat.decreasingInduction with
  | self => rw [H.push_refl]; exact (boundary H p X hX).1
  | of_succ i hi ih => rw [haul_next H p X hX hi]; dsimp only [Pass.onward]; rw [ih,H.push_next q _ hi]
theorem identity (s : Bool) (hP : ∀ m, m<M → H.w q m ≠ 0) (h : m ≤ M) :
    H.push q m M (global p s X)=(haul H q M p X hX m).total s (p.symbol _) :=by
  induction h using Nat.decreasingInduction with
  | self =>
    rw [H.push_refl]
    ext1 U
    simp only [Pass.total,totalL,global,(boundary H p X hX).1,(boundary H p X hX).2, Pi.zero_apply,map_zero,sum_const_zero,sub_zero]
  | of_succ i hi ih => rw [haul_next H p X hX hi, Pass.polymer _ _ _ _ _ (p.symbol _) s (p.flies s (H.step i q)) ((p.trace _).trans (p.trace _).symm) (hP i hi),← ih,H.push_next q _ hi]

include hX in
lemma exact_each (p : Pair N) (s : Bool) (x : Site (H.lattice M q)) (h : m ≤ M) : Density.volume (H.push q m M (each p s x X))=0:=by
  rw [H.volume_push q _ (each_cont _ _ _ hX) h, localized,mul_zero]
include hX in
lemma summed_output (p : Pair N) (s : Bool) (h : m≤M) :
    H.push q m M (global p s X)=∑ x : Site (H.lattice M q), H.push q m M (each p s x X) := by
  have he (l : Finset (Site (H.lattice M q))) : H.push q m M (∑ x ∈ l, each p s x X)=∑ x ∈ l, H.push q m M (each p s x X):=by
    induction l using Finset.induction_on with
    | empty =>
      rw [sum_empty,sum_empty]
      have ht:= H.add q (0: Density (H.lattice M q) N) 0 continuous_const continuous_const h
      rw [add_zero,left_eq_add] at ht -- fix
      exact ht
    | @insert x t ht ih => rw [sum_insert ht,sum_insert ht,H.add q _ (∑ x ∈ t, each p s x X) (each_cont p s x hX) (by rw [show ∑ x ∈ t, each p s x X = fun U => ∑ x ∈ t, each p s x X U from funext fun i => Finset.sum_apply i t _]; exact continuous_finsetSum _ fun i _=> each_cont p s i hX) h,ih]
  rw [summed]; exact he univ

lemma precise_vac (p : Pair N) {m q M : ℕ} (h : m≤M) (ht : M ≤ H.depth q) :
    (haul H q M p (H.actual q M) (H.actual_cont q ht) m).kernel=H.actual q m := by
  induction h using Nat.decreasingInduction with
  | self => exact (boundary ..).1
  | of_succ i hi ih => rw [haul_next H p _ _ hi]; dsimp only [Pass.onward]; rw [ih,H.actual_next q (lt_of_lt_of_le hi ht)]
end History
end YM.TorusPCAC.Ward
