import YM.TorusPCAC.Ward.Kernel

/-! # Passing global variations through actual Wilson kernel -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Ward
open QCD QCD.Grass QCD.Kit Finset Function
open scoped Matrix Topology BigOperators

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (Q : Matrix B A ℂ)

abbrev Z : Grass.Dirac A →ₗ[ℂ] Grass.Dirac B where
  toFun x := sheath 1 Q x
  map_add' x y:=by simp only [sheath,map_add,smul_add,add_mul]
  map_smul' a x:=by simp only [sheath,map_smul,smul_mul_assoc]; rw [smul_comm]; rfl

omit [DecidableEq A] in
lemma Z_left (x : Grass.Dirac A) : Z Q x=marginal A B (noise Q * near A B x) := by
  change sheath _ Q x=_; simp only [noise,sheath,Complex.ofReal_one, inv_one, one_pow, one_smul]; rw [(gauss_plus _).central _]

omit [DecidableEq A] in
lemma Z_far (x : Grass.Dirac A) (p : B) (s : Bool) : D s p (Z Q x)=marginal A B
    (D s (Sum.inr p) (noise Q)* near A B x) := by
  rw [Z_left,D, ← marg_cools,vary_mul,cool_silent,mul_zero,add_zero,cool_eq]

theorem transfer (x : Grass.Dirac A) (p : A) (s : Bool) : Z Q (D s p x)=∑ u : B, st s Q u p • D s u (Z Q x) := by
  have he:=marg_kills (bin s p) (noise Q* near A B x)
  rw [vary_mul, warm_survives,warm_eq, show grade (noise Q)=noise Q from gauss_plus ..] at he
  rw [← D,hot_noise] at he
  simp only [neg_mul, sum_mul,smul_mul_assoc,map_add,map_neg,map_sum,map_smul, ← Z_left, ← Z_far] at he
  exact ((eq_of_neg_add_eq_zero he).symm) -- check

theorem antiTransfer (x : Grass.Dirac A) (p : B) (s : Bool) : Z Q (avgAtom Q s p * x)= letter s p * Z Q x - sign s • D (!s) p (Z Q x) := by
  rw [Z_far,cool_noise]; simp only [Z_left]
  have he : sign s * sign s=1:=by cases s <;> simp [sign]
  rw [smul_mul_assoc,map_smul, smul_smul,he,one_smul, sub_mul,sub_mul,map_sub]
  rw [show marginal A B (letter s (Sum.inr p)*noise Q*near A B x)=letter s p*marginal A B (noise Q * near A B x) from
    (by rw [mul_assoc,letter,← cool_eq,marg_atom])]
  rw [map_mul (near A B), ((show Plus (noise Q) from gauss_plus _).central (near A B (avgAtom Q s p))).eq, mul_assoc]; abel

/-- `ψ→Aψ` or `bar→bar A`. `alpha` puts each in column notation. -/
def alpha (s : Bool) (a : Matrix A A ℂ) := if s then aᵀ else a

def hess (i j : A) := (D false i).comp (D true j)
omit [DecidableEq A] in
lemma hess_value (s : Bool) (a : Matrix A A ℂ) (x : Grass.Dirac A) :
    ∑ i, ∑ j, a i j • hess i j x = -(∑ i, ∑ j, alpha s a i j • sign s • (D s i (D (!s) j x))) := by
  cases s
  · simp [hess,alpha,sign,sum_neg_distrib]
  · simp only [hess,alpha,sign, ↓reduceIte, Bool.not_true,Matrix.transpose_apply,one_smul,LinearMap.comp_apply]
    rw [sum_comm]; simp_rw [D,anti_vary x (bin false _) (bin true _),smul_neg,sum_neg_distrib]

def rotation (s : Bool) (a : Matrix A A ℂ) : Grass.Dirac A →ₗ[ℂ] Grass.Dirac A where
  toFun x := ∑ i, ∑ j, alpha s a i j • (letter s j * D s i x)
  map_add' x y:=by simp only [map_add,mul_add,smul_add,sum_add_distrib]
  map_smul' k x:=by simp only [map_smul,mul_smul_comm, smul_sum]; simp_rw [smul_comm (alpha _ _ _ _) k]; rfl -- RHS semilinear?

lemma rotation_head (s : Bool) (a : Matrix A A ℂ) (x : Grass.Dirac A) : rotation s a x=a.trace • x - ∑ i, ∑ j, alpha s a i j • D s i (letter s j*x) := by
  simp only [rotation,LinearMap.coe_mk,AddHom.coe_mk,D,letter,vary_head,probe_ix, (bin_inj s).eq_iff]
  have he (i : A) : ∑ j, alpha s a i j • (if i=j then 1 else (0:ℂ)) • x= a i i • x := by cases s <;> simp [alpha,ite_smul,smul_ite]
  simp only [smul_sub, sum_sub_distrib,he,← sum_smul]; unfold Matrix.trace; rw [show ∑ x, a x x=(∑ i, a.diag i) from rfl]; abel

lemma rotation_killed (s : Bool) {a : Matrix A A ℂ} (h : a.trace=0) (x : Grass.Dirac A) : ber _ (rotation s a x)=0:=by
  rw [rotation_head,h]; simp only [D,zero_smul,map_sub,map_zero,map_sum,map_smul,integration,smul_zero,sum_const_zero,sub_zero]

variable (a : Matrix A A ℂ) (b : Matrix B B ℂ)
theorem commutes (s : Bool) (h : st s Q * alpha s a= alpha s b * st s Q) (ht : a.trace=b.trace)
    (x : Grass.Dirac A) : Z Q (rotation s a x)=rotation s b (Z Q x) - ∑ i, ∑ j, b i j • hess i j (Z Q x) := by
  let M := st s Q
  let R (i : B) (j : A) := D s i (Z Q (letter s j * x))
  rw [hess_value s,sub_neg_eq_add]
  simp_rw [rotation_head,ht,map_sub,map_sum,map_smul,transfer Q _ _ s,smul_sum]
  have he (i : B) : ∑ j : A, (M * alpha s a) i j • R i j =
      ∑ p : B, alpha s b i p • (D s i (letter s p * Z Q x) - sign s • D s i (D (!s) p (Z Q x))) := by
    rw [show M*alpha s a= _ from h]
    have hp (p : B) : ∑ j, M p j • R i j = (D s i (letter s p * Z Q x) - sign s • D s i (D (!s) p (Z Q x))) := by
      rw [← map_smul,← map_sub,← antiTransfer]; unfold R avgAtom; simp only [sum_mul,map_sum,smul_mul_assoc,map_smul]; rfl
    simp_rw [Matrix.mul_apply,sum_smul,mul_smul, ← hp,smul_sum]; exact sum_comm
  have hh : (∑ (i : A), ∑ j : A, ∑ p : B, alpha s a i j • M p i • R p j)= ∑ p : B, ∑ j, (M * alpha s a) p j • R p j := by
    simp_rw [Matrix.mul_apply,sum_smul,mul_smul, smul_comm (M _ _)]
    rw [sum_comm]; conv_rhs => rw [sum_comm];
    apply sum_congr rfl; intro j _; rw [sum_comm]
  change b.trace • Z Q x-(∑ (i : A), ∑ j, ∑ p, alpha s a i j • M p i • R p j)=_
  simp_rw [hh,he,smul_sub,sum_sub_distrib]; abel
  -- after sort
end YM.TorusPCAC.Ward
