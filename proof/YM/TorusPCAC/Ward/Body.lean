import YM.TorusPCAC.Ward.Flavor

/-!
# Connected flat-link spin derivatives

Give coefficient formula suitable for reading the tSig moment. It doesn't
use Gaussianity of sea, and isolates truly quartic interaction (i.e.
relative exponential cost through entire pushed density). Can use actual
normalized numerator/denominator here without seizing a particular pole.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Ward
open QCD QCD.Grass QCD.Lat Finite Finset Function NormedSpace
open scoped Matrix Topology BigOperators Kronecker Matrix.Norms.Frobenius

variable {A : Type*} [Fintype A]
lemma zeroR_one : zeroR (1:Alg A)=1:=by rw [← mono_empty]; exact Grass.read ..
lemma zeroR_mul (x y : Alg A) : zeroR (x*y)=zeroR x*zeroR y:=by
  have he (s t : Finset A) : zeroR (mono s*mono t)=zeroR (mono s)*zeroR (mono t):=by
    by_cases hs : s=∅
    · simp only [hs, mono_empty,one_mul,zeroR_one]
    rw [show zeroR (mono s*mono t)=0 from spectrum (layer_mul (homogeneous s) (homogeneous t)) _ (by
      rw [card_empty]; exact (Nat.add_pos_left (Finset.card_pos.mpr (nonempty_iff_ne_empty.mpr hs)) _).ne),
      show zeroR (mono s)=0 from read_other _ _ (Ne.symm hs),zero_mul]
  rw [← write x,← write y]; simp only [map_sum,map_smul,sum_mul,mul_sum, smul_mul_assoc,mul_smul_comm,he]
lemma zeroR_grade (x : Alg A) : zeroR (grade x)=zeroR x:=by
  have he (s : Finset A) : zeroR (grade (mono s))=zeroR (mono s):=by
    rw [grade_mono,map_smul]; by_cases h : s=∅
    · simp only [h,card_empty,pow_zero,one_smul]
    rw [show zeroR (mono s)=0 from read_other _ _ (Ne.symm h), smul_zero]
  rw [← write x]; simp only [map_sum,map_smul,he]
lemma zeroR_Minus {x : Alg A} (h : Minus x) : zeroR x=0 :=by
  have ht := zeroR_grade x; rw [(show grade x=-x from h),map_neg] at ht; exact neg_eq_self.mp ht
lemma zeroR_exp (x : Alg A) : zeroR (exp x)=Complex.exp (zeroR x) :=by
  let W : Alg A →ₐ[ℂ] ℂ:=
    { zeroR (A:=A) with
      map_one' := zeroR_one
      map_mul' := zeroR_mul
      map_zero' := map_zero zeroR
      commutes' := fun r=> by rw [Algebra.algebraMap_eq_smul_one]; change zeroR (r • (1:Alg A))=r; simp [zeroR_one] }
  rw [Complex.exp_eq_exp_ℂ]; exact map_exp W zeroR.continuous_of_finiteDimensional x -- check
lemma zeroR_unit (x : Alg A) (h : IsUnit x) : zeroR x≠0 := by
  have he : x * Ring.inverse x=1:=Ring.mul_inverse_cancel _ h
  apply left_ne_zero_of_mul; rw [← zeroR_mul,he,zeroR_one]; exact one_ne_zero

lemma opposite (x : Alg A) (i : A) : grade (vary i x)= - vary i (grade x):= by
  have hh (l : List A) : grade (vary i (l.map atom).prod) = - vary i (grade (l.map atom).prod):= by
    induction l with
    | nil => simp only [List.map_nil,List.prod_nil,map_one,vary_one,map_zero,neg_zero]
    | cons y l h => simp only [List.map_cons,List.prod_cons,vary_head,map_mul,grade_atom,map_neg,map_sub,map_smul,h,neg_mul, mul_neg,neg_neg]
  have ht (s : Finset A) : grade (vary i (mono s)) = -vary i (grade (mono s)):=by
    obtain ⟨f,-,-,he⟩:= Grass.expression s; rw [he]; simpa only [List.map_ofFn] using hh (List.ofFn f)
  rw [← write x]; simp only [map_sum,map_smul,ht, smul_neg,sum_neg_distrib]
lemma no_lonely {f : Alg A} (h : Plus f) (x : A) : zeroR (vary x f)=0:= zeroR_Minus (show grade _=-_ from by rw [opposite,(show grade f=f from h)])
lemma fixed {f : Alg A} (h : Plus f) (x y : A) : Plus (vary x (vary y f)):=by unfold Plus; rw [opposite,opposite,(show grade f=f from h),map_neg,neg_neg]

/-- including all sign orientations of left derivative. -/
def two (f : Alg A) (x y : A) := zeroR (vary x (vary y f))
def four (f : Alg A) (x y z t : A) := zeroR (vary x (vary y (vary z (vary t f))))

def log2 (f : Alg A) (x y : A) := two f x y / zeroR f
def log4 (f : Alg A) (x y z t : A) := four f x y z t / zeroR f -
  (log2 f x y * log2 f z t + log2 f x t * log2 f y z - log2 f x z * log2 f y t)

lemma exp_plus {e : Alg A} (h : Plus e) : Plus (NormedSpace.exp e) := by unfold Plus; rw [map_weight,(show grade e=e from h)]

lemma two_mul_form {e : Alg A} (x y : A) (f : Alg A) (h : Plus e) : two (e*f) x y=two e x y * zeroR f+zeroR e*two f x y := by
  unfold two
  simp only [vary_mul, map_add,(show grade e=e from h), zeroR_mul, opposite, no_lonely h,map_neg,zero_mul,neg_zero, add_zero,zero_add]

lemma log2_good {e : Alg A} (x y : A) (a : ℂ) (ha : a ≠ 0) (h : Plus e) : log2 (a • exp e) x y=two e x y:=by
  have he := show zeroR (exp e)≠0 by rw [zeroR_exp]; exact Complex.exp_ne_zero _
  unfold log2 two
  simp only [map_smul,varies_exp y e h, vary_mul, (show grade (exp e)=_ from exp_plus h), map_add,zeroR_mul,no_lonely (exp_plus h), zero_mul,zero_add,smul_eq_mul]; field_simp

lemma log4_good {e : Alg A} (x y z t : A) (a : ℂ) (ha : a ≠ 0) (h : Plus e) : log4 (a • exp e) x y z t=four e x y z t:=by
  let f:=exp e; have hf:= exp_plus h
  have he := show zeroR (exp e)≠0 by rw [zeroR_exp]; exact Complex.exp_ne_zero _
  simp_rw [log4,log2_good _ _ _ ha h]
  have ht (x y : A) : zeroR (vary x (vary y (exp e)))=zeroR (exp e)*two e x y:=by
    have hx := log2_good x y 1 one_ne_zero h; rw [one_smul,log2,div_eq_iff he] at hx
    rw [mul_comm]; exact hx
  unfold four
  rw [map_smul (vary t)]; simp only [map_smul, varies_exp t e h, vary_mul,map_add,zeroR_mul, opposite, (show grade (exp e)=exp e from hf), map_neg,no_lonely h,no_lonely hf,no_lonely (fixed hf _ _),ht,neg_zero,zero_mul,zero_add,add_zero, smul_eq_mul]
  unfold two; field_simp; ring

lemma four_mul_form {e : Alg A} (x y z t : A) (f : Alg A) (h : Plus e) : four (e*f) x y z t=four e x y z t*zeroR f+zeroR e*four f x y z t+
     two e x y * two f z t + two e z t * two f x y + two e x t * two f y z + two e y z * two f x t - two e x z * two f y t -two e y t * two f x z := by
  unfold four two
  simp only [vary_mul,map_add,(show grade e=e from h),opposite,zeroR_mul,no_lonely h,map_neg,no_lonely (fixed h _ _),neg_zero,zero_mul,add_zero,zero_add]
  ring
end YM.TorusPCAC.Ward
