import YM.Heron.Peak
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (fromCenter)
open Maxwell (grad)
variable (s:Ortho.Skew)(A:TinG)(Γ:ℝ→EuPin)(hΓ:EuPin.Path s Γ) (B:EuPin)(t:Bool)(j k:Axis)
noncomputable def rune (a:Spike): Faces→ₗ[ℂ]Faces:=a.mulVecLin
noncomputable def holdG (s:Ortho.Skew)(A:TinG) : Faces →L[ℝ] Faces:= ((rune (walt A s)).restrictScalars ℝ).toContinuousLinearMap
local notation "H"=>holdG s A
local notation "II"=>s.val
lemma nut (x:Faces): holdG s A x= (1/4:ℝ) • ∑ i:Axis,∑ j:Axis, II j i • cog A i (cog A j x):=by
   change walt A s*ᵥ x=_; unfold walt; have he (r:ℝ)(v:Faces): (r:ℂ) • v=r • v:=rfl; rw [Matrix.smul_mulVec]; have hs {ι:Type}[Fintype ι](F:ι→Spike)(X:Faces) : (∑ i, F i)*ᵥ X= ∑ i,F i*ᵥ X:=by -- Mathlib
        ext l; simp_rw[Matrix.mulVec,dotProduct, Finset.sum_apply, Matrix.sum_apply]; simp only[Finset.sum_mul]; rw[Finset.sum_comm]; rfl
   simp_rw [hs,Matrix.smul_mulVec, cogP, Matrix.mulVec_mulVec, he]; rw [← show (↑((1/4):ℝ):ℂ)=1/4 from by norm_num]; exact he ..
variable (F:Spins)(x y:E4){U:Set E4}(hx:x∈ U)(hU:IsOpen U)
local notation "G"=> fromCenter II y
local notation "L"=> twistS A G F
lemma helm : Seam (fromCenter s.val y):=by
    refine ⟨Maxwell.Free.center_smooth _ _,fun x a b=>?_⟩; simp only [Maxwell.Free.center_grad]; exact (Complex.ofReal_injective (by rw[Complex.ofReal_neg]; exact skewL s b a))
lemma goes (x:E4): twistS A (fromCenter II y) F x=(∑ i:Axis, fromCenter II y i x • grad i F x)+holdG s A (F x):=by rw[nut]; simp only [twistS, Maxwell.Free.center_grad] -- rewrite twist directly
lemma life(hf: ContDiffAt ℝ ∞ F x): ContDiffAt ℝ ∞ L x:=by
    rw [funext (goes s A F y)]; apply ContDiffAt.add
    · exact ContDiffAt.sum fun i _=> ((helm s y).smooth i).contDiffAt.smul (Maxwell.grad_smooth i hf (by simp))
    exact (H).contDiff.contDiffAt.comp x hf
lemma shifts(hf:ContDiffAt ℝ ∞ F x):grad j L x = twistS A G (grad j F) x+∑ k:Axis, II k j • grad k F x:=by
    rw [funext (goes s A F y), goes s A (grad j F)];
    have hg(i:Axis):= Maxwell.grad_smooth i (m:=∞) hf (by simp); let f(i:Axis):E4→Faces:=fun t=> fromCenter II y i t • grad i F t; have hv(i:Axis): ContDiffAt ℝ ∞ (f i) x:= ((helm s y).smooth i).contDiffAt.smul (hg i); have hc:= (H).contDiff.contDiffAt.comp x hf;
    change fderiv ℝ (fun x=>(∑ i:Axis,f i x)+((H) ∘ F) x) x _= _; rw [fderiv_fun_add (DifferentiableAt.fun_sum fun i _=>(hv i).differentiableAt (by simp)) (hc.differentiableAt (by simp))]; change fderiv ℝ (fun x=>∑ i:Axis,f i x) _ _+grad j ((H) ∘ F) x=_; rw [Maxwell.grad_linear _ hf, fderiv_fun_sum _]; swap; · intro i _; exact (hv i).differentiableAt (by simp)
    rw [_root_.sum_apply]; have ht(i): fderiv ℝ (f i) x (basis j)=fromCenter II y i x • grad i (grad j F) x+ II i j • grad i F x :=by
        unfold f; rw [fderiv_fun_smul ((helm s y).smooth i|>.differentiable (by simp) x) ((hg i).differentiableAt (by simp))]; change fromCenter _ _ _ _ • grad j (grad i F) _ + grad j (fromCenter _ _ _) _ • grad i F x= _; rw [Maxwell.grad_comm (hf.of_le (WithTop.coe_le_coe.mpr le_top)) j i,Maxwell.Free.center_grad]
    simp_rw [ht,Finset.sum_add_distrib]; abel
include hΓ
noncomputable def turnG(B:EuPin)(t:Bool): Faces →ₗ[ℂ] Faces:= rune (splice t B)
lemma actO (v:Faces): HasDerivAt (fun x:ℝ=> turnG (Γ x) t v) (holdG s (formT t) v) 0:=by
    let GH:Spike→ₗ[ℝ] Faces:= { toFun:=fun S=> S *ᵥ v, map_add':=fun a b=> Matrix.add_mulVec .., map_smul':=fun z x=> Matrix.smul_mulVec ..}; exact GH.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) (jenna s Γ hΓ t)
lemma uno (v:Faces): turnG (Γ 0) t v=v:=by
   change splice t _*ᵥ v= v; rw[stems s Γ hΓ t _ hΓ.1,Matrix.one_mulVec]
end YM.Heron
#print axioms YM.Heron.shifts
#print axioms YM.Heron.actO
