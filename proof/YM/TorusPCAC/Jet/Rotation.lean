import YM.TorusPCAC.Jet.Pairs
import YM.TorusPCAC.Spin.Components

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Clifford pair kernel law plus the exact derivative indices -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet
open QCD QCD.Lat Finset Function MeasureTheory TensorProduct Spin
open scoped Matrix Topology BigOperators Kronecker TensorProduct Matrix.Norms.Frobenius
open MvPolynomial

def sgn (s: Signed) (a: Axis) : ℂ:= if s.flip a then -1 else 1 -- notation?
def hit (a:Axis) : Order:=Finsupp.single a 1
lemma unturned (R : Ortho) : rotateMono R 0=MvPolynomial.monomial 0 1:=by simp [rotateMono]
lemma hinge (R : Signed) (i : Axis) : rotateMono R.ortho (hit i)=MvPolynomial.monomial (hit (R.perm i)) (sgn R i):=by
  unfold rotateMono hit; rw [Finset.prod_eq_single i];
  · rw [Finsupp.single_eq_same,pow_one, sum_eq_single (R.perm i)]
    · dsimp only [Signed.ortho]; rw [Signed.matrix_at]; simp only [if_true]; rw [MvPolynomial.X, C_mul_monomial,mul_one]; unfold sgn; split <;> simp
    · intro b _ h; rw [show R.ortho.val b i=R.matrix b i from rfl,R.matrix_at,if_neg (Ne.symm h)]; simp
    simp
  · intro b _ h; rw [Finsupp.single_eq_of_ne h, pow_zero]
  simp

variable (p : Pin)
variable (i j : Flav) (u v : Pinor) (k l : Hue) {t t' s s' : Order} {A B : ℂ}
variable (h : rotateMono p.val.1 t=MvPolynomial.monomial t' A) (hA:A≠0) (hp:rotateMono p.val.1 s=MvPolynomial.monomial s' B) (hB:B≠0)
include h hA
lemma tiltedψ : rotate p (leg i u k t) =∑ r : Pinor, (A*p.val.2⁻¹.val u r) • leg i r k t':=by
  unfold rotate leg; rw [spin_map_slot]; simp only [↓reduceIte,h]; rw [MvPolynomial.support_monomial,if_neg hA, sum_singleton, coeff_monomial]; simp only [if_true,map_sum,map_smul]; simp_rw [TensorProduct.tmul_sum,TensorProduct.tmul_smul]; rfl
lemma tiltedB : rotate p (rim i u k t) =∑ r : Pinor, (A*p.val.2.val r u) • rim i r k t' :=by
  unfold rotate rim; rw [spin_map_slot]; simp only [reduceCtorEq,↓reduceIte,h]; rw [MvPolynomial.support_monomial,if_neg hA, sum_singleton, coeff_monomial]; simp only [if_true,map_sum,map_smul]; simp_rw [TensorProduct.tmul_sum,TensorProduct.tmul_smul]; rfl

-- useful general contraction rearrangement when rows map linearly into fixed spin matrix.
omit h hA in
lemma points2 (Z:Spike) (a b c d : Order) (P R:Spike) (K:Pol→ₐ[ℂ] Pol)
    (h:∀ u k, K (rim i u k a)=∑ r : Pinor,P r u • rim i r k c)
    (hp:∀ u k, K (leg j u k b)=∑ r : Pinor,R u r • leg j r k d) :
    K (crowd i j a b Z)=crowd i j c d (P*Z*R) :=by
  have he (x y : Pinor): K (duo i j a b x y)=∑ u : Pinor,∑ v : Pinor,(P u x*R y v) • duo i j c d u v:=by
    unfold duo; simp_rw [element, map_sum,map_mul,h,hp,sum_mul,mul_sum,smul_sum]
    rw [sum_comm]; refine sum_congr rfl fun k _=> ?_; rw [sum_comm]; simp_rw [smul_mul_smul_comm]
  simp only [crowd,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul]; simp_rw [he,smul_sum, Matrix.mul_apply,Finset.sum_mul, sum_smul,smul_smul]
  let f:=fun (x y u v:Pinor)=> (Z x y*(P u x*R y v)) • duo i j c d u v
  have hQ: (∑ x,∑ y,∑ u,∑ v,f x y u v)=(∑ u,∑ v,∑ x,∑ y, f x y u v):=by
    have hp:=sum_comm (s:=univ) (t:=univ) (f:=fun (x y:Pinor × Pinor)=>f x.1 x.2 y.1 y.2); simp only [Fintype.sum_prod_type (α₁:=Pinor) (α₂:=Pinor)] at hp; exact hp
  apply hQ.trans; unfold f; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; rw [sum_comm]; apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _; ring_nf
include hp hB
lemma tilted (Z : Spike) : rotate p (crowd i j t s Z)=(A*B) • crowd i j t' s' (Spin.MatrixColor.turn p Z) := by
  simp_rw [points2 i j Z t s t' s' (A • p.val.2.val) (B • p.val.2⁻¹.val) (rotate p) (fun u k=>tiltedB p i u k h hA) (fun u k=> tiltedψ p j u k hp hB), Matrix.smul_mul, Matrix.mul_smul,map_smul]
  rw [smul_smul]; rfl
omit h hA hp hB
lemma pure_rotation (Z:Spike) : rotate p (Jet.bilinear i j Z)= Jet.bilinear i j (Spin.MatrixColor.turn p Z):=by rw [← plain0, tilted p i j (unturned _) one_ne_zero (unturned _) one_ne_zero,mul_one,one_smul,plain0]
end YM.TorusPCAC.Jet

#print axioms YM.TorusPCAC.Jet.pure_rotation
