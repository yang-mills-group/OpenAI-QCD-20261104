import YM.QCD.Grass.SD

/-!
# Dirac Gaussian Wick for ordered slots

Exact signs by Berezin convention. Includes unequal/degenerate insertions. Here normalized
Gaussian uses a nonzero determinant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Function Finset
open scoped BigOperators Topology Matrix
variable {A : Type*} [Fintype A]

def straw (x : A→ℂ) : Dirac A := ∑ i, x i • psi i
def brin (x : A→ℂ) : Dirac A := ∑ i, x i • bar i

def bundle : {k : ℕ} → (Fin k → A→ℂ) → Dirac A
  | 0, _ => 1
  | k+1, Q => straw (Q 0)*bundle (fun i : Fin k => Q i.succ)

def twigs : {k : ℕ} → (Fin k → A→ℂ) → Dirac A
  | 0, _ => 1
  | k+1, Q => twigs (fun i : Fin k => Q i.succ)*brin (Q 0)

variable {k : ℕ}
lemma next_b (Q : Fin (k+1)→ A→ℂ) : bundle Q=straw (Q 0)*bundle (fun i : Fin k => Q i.succ) := by rw [bundle]
lemma next_t (Q : Fin (k+1)→ A→ℂ) : twigs Q=twigs (fun i : Fin k => Q i.succ)*brin (Q 0) := by rw [twigs]
lemma down_straw (x : A→ℂ) : grade (straw x)=-straw x := by simp [straw,psi,grade_atom]
lemma down_brin (x : A→ℂ) : grade (brin x)=-brin x := by simp [brin,bar,grade_atom]
lemma measures_brin (x : A→ℂ) (i : A) : vary (Sum.inr i) (brin x)=x i • 1 := by
  unfold brin; rw [map_sum,sum_eq_single i]
  · rw [map_smul]; simp [bar]
  · intro j _ h; rw [map_smul,bar,vary_off _ _ (Sum.inr_injective.ne (Ne.symm h)),smul_zero]
  simp
lemma none_straw (x : A→ℂ) (i : A) : vary (Sum.inr i) (straw x)=0 := by
  unfold straw; rw [map_sum]; exact sum_eq_zero fun j _ => by rw [map_smul,psi,vary_off _ _ (by simp),smul_zero]
lemma folds (k : ℕ) (Q P : Fin k → A→ℂ) : grade (bundle Q*twigs P)=bundle Q*twigs P := by
  induction k with
  | zero => simp [bundle,twigs]
  | succ k ih =>
    rw [next_b,next_t]
    have he (x y a b : Dirac A) : x*y*(a*b)=x*(y*a)*b := by simp only [mul_assoc]
    rw [he,map_mul,map_mul,ih, down_straw,down_brin,neg_mul,neg_mul_neg]

lemma splitting (Q : Fin k→ A→ℂ) (P : Fin (k+1)→ A→ℂ) (i : A) :
    vary (Sum.inr i) (bundle Q*twigs P)=∑ j, ((-1:ℂ)^(j.val)*P j i) • (bundle Q*twigs (fun a => P (j.succAbove a))) := by
  induction k with
  | zero => simp [bundle,twigs,measures_brin]
  | succ k ih =>
    rw [next_t P,← mul_assoc,vary_mul, measures_brin, folds, next_b Q, mul_assoc (straw _) (bundle _) (twigs _),vary_mul,
      ih,none_straw,down_straw,zero_mul,zero_add,neg_mul]
    conv_rhs => rw [Fin.sum_univ_succ]
    rw [Fin.val_zero,pow_zero,one_mul, mul_smul_comm,mul_one,add_comm, Fin.succAbove_zero,
      mul_assoc (straw _) (bundle _) (twigs _)] -- check
    congr 1; rw [neg_mul,mul_sum,sum_mul,← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [next_t fun a => P (j.succ.succAbove a)]
    simp only [mul_assoc, Fin.succ_succAbove_succ,Fin.succ_succAbove_zero, Fin.val_succ,pow_succ', neg_mul,one_mul, neg_smul]
    simp only [← mul_assoc,mul_smul_comm,smul_mul_assoc]

variable [DecidableEq A]

def seen (M : Matrix A A ℂ) : Dirac A→ₗ[ℂ] ℂ := M.det⁻¹ • (ber A).comp (LinearMap.mulLeft ℂ (gauss M))
lemma seen_apply (M : Matrix A A ℂ) (x : Dirac A) : seen M x=M.det⁻¹ * ber A (gauss M*x) := rfl
lemma seen_one {M : Matrix A A ℂ} (h : IsUnit M.det) : seen M 1=1 := by rw [seen_apply,mul_one,det_amplitude, inv_mul_cancel₀ h.ne_zero]
lemma integrate_rows (M : Matrix A A ℂ) (x : Dirac A) (i : A) : seen M (straw (M i)*x) = seen M (vary (Sum.inr i) x) := by rw [seen_apply, straw, answer]; rfl

omit [DecidableEq A] in
lemma straw_row (M : Matrix A A ℂ) (u : A→ℂ) : straw (Matrix.vecMul u M) = ∑ j, u j • straw (M j) := by
  simp only [straw, Matrix.vecMul,dotProduct,smul_sum,sum_smul,smul_smul]; exact sum_comm
lemma contracts (M : Matrix A A ℂ) (h : IsUnit M.det) (x : Dirac A) (u : A→ℂ) :
    seen M (straw u*x)=∑ j, Matrix.vecMul u M⁻¹ j*seen M (vary (Sum.inr j) x) := by
  conv_lhs => rw [← Matrix.vecMul_one u,← Matrix.nonsing_inv_mul _ h, ← Matrix.vecMul_vecMul] -- check orientation
  simp only [straw_row,sum_mul,map_sum,smul_mul_assoc,map_smul,integrate_rows,smul_eq_mul]

def lineup (M : Matrix A A ℂ) (Q P : Matrix (Fin k) A ℂ) := Q*M*P.transpose
omit [DecidableEq A] in
lemma row_l (M : Matrix A A ℂ) (Q P : Matrix (Fin k) A ℂ) (i j : Fin k) :
    lineup M Q P i j = ∑ a, Matrix.vecMul (Q i) M a*P j a := rfl -- check
omit [DecidableEq A] in
lemma preserve_l (M : Matrix A A ℂ) (Q P : Matrix (Fin (k+1)) A ℂ) (j : Fin (k+1)) :
    lineup M (fun i => Q i.succ) (fun i => P (j.succAbove i))=(lineup M Q P).submatrix Fin.succ j.succAbove := rfl
lemma wick (M : Matrix A A ℂ) (h : IsUnit M.det) (k : ℕ) (Q P : Matrix (Fin k) A ℂ) :
    seen M (bundle Q*twigs P)=(lineup M⁻¹ Q P).det := by
  induction k with
  | zero => simp [bundle,twigs, seen_one h]
  | succ k ih =>
    rw [next_b,mul_assoc,contracts _ h, Matrix.det_succ_row_zero]
    simp only [splitting,map_sum,map_smul,smul_eq_mul,mul_sum, ← preserve_l]
    rw [sum_comm]; apply sum_congr rfl; intro j _
    rw [row_l, mul_sum,sum_mul]; exact sum_congr rfl fun a _ => by rw [ih]; ring

lemma twist_charge (M : Matrix A A ℂ) {c : ℂ} (h : c≠0) (x) :
    seen M (adapter (c • (1:Matrix A A ℂ)) (c⁻¹ • 1) x)=seen M x := by
  let f := adapter (c • (1:Matrix A A ℂ)) (c⁻¹ • 1)
  have he : f (gauss M)=gauss M := by dsimp only [f]; rw [gauss_map]; simp [h]
  have ht (y) : ber A (f y)=ber A y := by dsimp only [f]; rw [volume_map]; simp [h]
  rw [seen_apply,seen_apply]; change M.det⁻¹*ber A (gauss M * f x)=_
  conv_lhs => rw [← he,← map_mul, ht]
lemma chargeFactor (c d : ℂ) (Q : Fin k→A→ℂ) : adapter (c • (1:Matrix A A ℂ)) (d • 1) (bundle Q)=c^k • bundle Q := by
  induction k with
  | zero => simp [bundle]
  | succ k ih =>
    rw [next_b,map_mul,ih]
    have he (x : A→ℂ) : adapter (c • (1:Matrix A A ℂ)) (d • 1) (straw x)=c • straw x := by simp [straw,adapt_psi,Matrix.one_apply,ite_smul,smul_sum,smul_smul,mul_comm c]
    rw [he,mul_smul_comm,smul_mul_assoc,pow_succ,mul_smul]
lemma chargeFactor' (c d : ℂ) (Q : Fin k→A→ℂ) : adapter (c • (1:Matrix A A ℂ)) (d • 1) (twigs Q)=d^k • twigs Q := by
  induction k with
  | zero => simp [twigs]
  | succ k ih =>
    rw [next_t,map_mul,ih]
    have he (x : A→ℂ) : adapter (c • (1:Matrix A A ℂ)) (d • 1) (brin x)=d • brin x := by simp [brin,adapt_bar,Matrix.one_apply,ite_smul,smul_sum,smul_smul,mul_comm d]
    rw [he,smul_mul_assoc,mul_smul_comm,pow_succ,mul_smul]
lemma charged {m n : ℕ} (M : Matrix A A ℂ) (h : m≠n) (Q : Matrix (Fin m) A ℂ) (P : Matrix (Fin n) A ℂ) :
    seen M (bundle Q*twigs P)=0 := by
  by_contra hz
  have he := twist_charge M (c:=2) (by norm_num) (bundle Q*twigs P)
  rw [map_mul,chargeFactor, chargeFactor', smul_mul_assoc,mul_smul_comm,smul_smul,map_smul,smul_eq_mul] at he
  have hh := mul_right_cancel₀ hz (he.trans (one_mul _).symm)
  rw [inv_pow, mul_inv_eq_one₀] at hh -- check
  · exact h (Nat.pow_right_injective (by omega : (2:ℕ)≥2) (by exact_mod_cast hh)) -- check
  norm_num
end YM.QCD.Grass
