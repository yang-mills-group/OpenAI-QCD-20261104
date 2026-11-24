import YM.Hail.Swell
import YM.Next.MAXWELL.Force
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
abbrev Faces := Pinor→ℂ
abbrev Spins:= E4→ Faces
abbrev TinG:= Axis→ Spike
def TrueC(T:TinG):Prop:=∀ i j:Axis,T i*T j+T j*T i= if i=j then (2:ℂ) • (1:Spike) else 0
local notation "Q"=> Faces
local notation "g"=> gamma
lemma learn : TrueC gamma:=by
    intro i j; split <;> rename_i h; · subst j; rw[Lat.gamma_sq,two_smul]
    rw[clifford h]; abel
variable (A:TinG)(hc:TrueC A) (i j k:Axis)
noncomputable def FlipT (A:TinG):TinG:=fun i=>(A i).transpose
local notation "B"=> FlipT A
include hc
lemma flips :TrueC B:=by
    intro i j; change _+_=_; have h:=congr_arg Matrix.transpose (hc j i); simp only[Matrix.transpose_add,Matrix.transpose_mul] at h; unfold FlipT; rw[h]; by_cases he:i=j; · subst j; simp
    simp [he,Ne.symm he]
omit hc
noncomputable def pulseR (i:Axis): Module.End ℂ Faces:= Matrix.mulVecLin (A i)
noncomputable def cog(i:Axis): Q →L[ℝ] Q := ((pulseR A i).restrictScalars ℝ).toContinuousLinearMap
noncomputable def slash(i:Axis)(x:Q): Q:= cog A i x
lemma cogP (v:Q): cog A i v=A i *ᵥ v:=rfl
local notation "R"=> cog A
local notation "P"=> cog B
lemma flip_mul(v r:Q): (P i v) ⬝ᵥ r= v ⬝ᵥ R i r := by rw [cogP,cogP,FlipT,Matrix.mulVec_transpose]; exact (Matrix.dotProduct_mulVec ..).symm
noncomputable def enD (A:TinG)(F:Spins)(x:E4): Q:=∑ i:Axis,cog A i (Maxwell.grad i F x)
variable (F:Spins) {x:E4} (h:ContDiffAt ℝ ∞ F x)
include h
open Maxwell (grad)
lemma stance : ContDiffAt ℝ ∞ (enD A F) x:= ContDiffAt.sum fun i _=> (cog A i).contDiff.contDiffAt.comp x (Maxwell.grad_smooth i (m:=∞) h (by simp))
lemma rose : grad i (enD A F) x = ∑ j:Axis,R j (grad i (grad j F) x):=by
    change fderiv ℝ (fun x=> ∑ i:Axis,cog A i (grad i F x)) x _= _; rw [fderiv_fun_sum]; rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro j _; exact Maxwell.grad_linear (cog A j) (Maxwell.grad_smooth j h (by simp)) i
    intro j _; exact ((cog A j).contDiff.contDiffAt.comp x (Maxwell.grad_smooth j (m:=∞) h (by simp))).differentiableAt (by simp) -- Q InnerProduct? Pi sup NO; grad_sum_f requires Inner!
include hc
variable (X:Q) (c:ℂ)
omit h
lemma struck : cog A i (cog A j X)+cog A j (cog A i X) = if i=j then (2:ℂ) • X else 0:=by
    simp only [cogP]; rw[Matrix.mulVec_mulVec,Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hc]; split_ifs; · rw[Matrix.smul_mulVec,Matrix.one_mulVec]
    rw[Matrix.zero_mulVec]
include h
lemma tower : enD A (enD A F) x = ∑ i:Axis,grad i (grad i F) x :=by
    -- use stem
    let Q'(i j:Axis):=cog A i (cog A j (grad i (grad j F) x)); let K:=enD A (enD A F) x
    have hx:K=∑ i:Axis,∑ j:Axis,Q' i j:=by change ∑ i:Axis,R i _=_; simp_rw [rose A _ _ h, _root_.map_sum]; rfl
    apply smul_right_injective Q (by norm_num : (2:ℂ) ≠ 0)
    change (2:ℂ) • K= _ • _; rw [show ((2:ℂ) • K) =(∑ i:Axis, ∑ j:Axis,(Q' i j+ Q' j i)) from (?_)];
    · simp_rw [show ∀ i j:Axis, Q' i j+Q' j i= if i=j then (2:ℂ) • grad i (grad j F) x else 0 from fun i j=>by unfold Q'; nth_rw 1 [Maxwell.grad_comm (h.of_le (WithTop.coe_le_coe.mpr le_top)) j i]; exact struck A hc i j _]; simp [Finset.smul_sum]
    rw [hx,two_smul,Finset.sum_comm (f:=Q')]; simp_rw [Finset.sum_add_distrib]; rw [Finset.sum_comm (f:=fun i j=> Q' j i)] -- orient
end YM.Heron
#print axioms YM.Heron.tower
