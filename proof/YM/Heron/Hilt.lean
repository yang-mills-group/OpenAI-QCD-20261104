import YM.Heron.Ajax
import YM.Work.A13
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Maxwell (grad)
noncomputable def walt(T:TinG)(s:Ortho.Skew):Spike:= ((1/4:ℂ) • ∑ i:Axis,∑ j:Axis,(s.val j i:ℂ) • (T i * T j))
variable (s:Ortho.Skew)(A:TinG)(hc:TrueC A)(Γ:ℝ→EuPin)(hΓ:EuPin.Path s Γ)(i j k:Axis)
local notation "X"=> A
local notation "Y"=> -(walt A s)
local notation "S★"=> s.val
set_option quotPrecheck false
local notation "μ" i:arg j:arg =>(s.val i j:ℂ)
lemma skewL : μ i j = -(μ j i):=by
    rw[← Complex.ofReal_neg]; congr 1; have ht:=s.property; change (S★)ᵀ = -(S★) at ht; exact congr_fun (congr_fun ht j) i
lemma neutral_h : μ i i=0:=by have h:=skewL s i i; linear_combination h/2
lemma dualH : (walt A s).transpose= -walt (FlipT A) s:=by
    unfold walt; simp only [Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_mul]; nth_rw 1[Finset.sum_comm]; rw [← smul_neg, ← Finset.sum_neg_distrib]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; nth_rw 1[skewL s i j]; rw [neg_smul]; rfl
include hc
lemma snap (i j k:Axis): A i*A j*A k-A k*(A i*A j)= (if j=k then (2:ℂ) • A i else 0)-(if k=i then (2:ℂ) • A j else 0):=by
   rw [show (if j=k then _ else (_:Spike))=A i*(A j*A k+A k*A j) from (by rw [hc]; split <;> simp [Matrix.mul_smul]), show (if k=i then (2:ℂ) • A j else 0)= (A k*A i+A i*A k)*A j from (by rw [hc]; split<;>simp[Matrix.smul_mul])]; simp only[mul_add, add_mul,Matrix.mul_assoc]; abel
lemma fleet : Y *A k-A k*Y=∑ j:Axis,(μ j k) • A j:=by
    unfold walt; simp only [neg_mul,mul_neg,Matrix.smul_mul,Matrix.mul_smul,Finset.sum_mul,Finset.mul_sum]; rw [show -((1/4:ℂ) • _) - -((1/4:ℂ) • _) = -((1/4:ℂ) • ((∑ i:Axis,∑ j:Axis,(μ j i) • (A i*A j*A k)) - ∑ i:Axis,∑ j:Axis,(μ j i) • (A k*(A i*A j)))) from (by rw [smul_sub]; abel)]; simp_rw[← Finset.sum_sub_distrib, ← smul_sub, snap A hc _, smul_sub, smul_ite, smul_zero, Finset.sum_sub_distrib,Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]; rw[Finset.sum_comm (f:=fun i j:Axis=> if k=i then (μ j i) • ((2:ℂ) • A j) else 0)]; simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte];
    rw[← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; nth_rw 1[skewL s k j]; module
omit hc
include hΓ
lemma cChair : cΩ Γ 0=1:=by unfold cΩ; rw[hΓ.1]; rfl
lemma cRot (x:E4) : HasDerivAt (fun t=> Ortho.move ((Γ t).coord) x) (M4.move (s.val) x) 0:=by
    simp_rw[hΓ.2.2]; have he:=Work.A13.hasDerivAt_move s x 0; rw[Work.A13.oneParameter_zero,Ortho.move_one] at he; exact he
lemma cSpan : HasDerivAt (fun t=> (Γ t).coord.val i j) (s.val i j) 0 :=by
     have ht := (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp_hasDerivAt 0 (cRot s Γ hΓ (basis j)); simpa [Function.comp_def, Ortho.move] using ht
noncomputable def sheet(s:Ortho.Skew)(Γ:ℝ→EuPin):Spike:= deriv (cΩ Γ) 0
local notation "V"=> cΩ Γ
local notation "D"=> sheet s Γ
lemma horn :HasDerivAt V D 0:=(moss s Γ hΓ).hasDerivAt
lemma shineL (i:Axis): D*gamma i-gamma i*D=∑ j:Axis,(μ j i) • gamma j:=by
    let x:=basis i; have he(t:ℝ) :V t*gamma i= Massive.slash (Ortho.move (Γ t).coord x)* V t:=by
         rw[← show Massive.slash x= gamma i from (by simp [Massive.slash,x, basis_eq,ite_smul])]; exact ((euPin_iff _).mp (Γ t).property).2 x
    let T:E4→ₗ[ℝ]Spike:= {toFun:=Massive.slash,map_add':=fun x y=>by simp [Massive.slash,PiLp.add_apply,add_smul,Finset.sum_add_distrib],map_smul':=fun r y=>by simp only[Massive.slash,Finset.smul_sum, PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]; apply Finset.sum_congr rfl; intro i _; rw[Complex.ofReal_mul]; exact mul_smul (r:ℂ) _ _}; let F:= T.toContinuousLinearMap
    let H:= fun t=> Ortho.move (Γ t).coord x; have hd:= (horn s Γ hΓ).mul_const (gamma i); have hp:= (F.hasFDerivAt.comp_hasDerivAt (0:ℝ) (cRot s Γ hΓ x)).mul (horn s Γ hΓ); have hv : D* gamma i = F (M4.move s.val x)*V 0+ F (H 0)*D := by apply hd.unique; apply hp.congr_of_eventuallyEq; exact Eventually.of_forall he
    have hh:F (H 0)=gamma i:=by have h1:= cChair s Γ hΓ; have ht:=he 0; rw[h1,one_mul,mul_one] at ht; exact ht.symm
    rw [hh,cChair s Γ hΓ,mul_one] at hv; rw [hv, add_sub_cancel_right]; change Massive.slash _=_; apply Finset.sum_congr rfl; intro k _; congr 1; simp [x]
end YM.Heron
#print axioms YM.Heron.shineL
#print axioms YM.Heron.fleet
