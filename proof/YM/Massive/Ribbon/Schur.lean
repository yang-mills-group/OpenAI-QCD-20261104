import YM.Massive.Ribbon.Clifford
import Mathlib.LinearAlgebra.Matrix.PosDef
/-! # At most a double lift. `adj` uses transpose signs compatible with the hypercube Spin generators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Clifford
open QCD QCD.Lat Lattice Wilson Mink Lorentz Function Matrix QCD.Revolve
open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology Kronecker ComplexOrder

lemma Cunit_ne : C≠0:=by intro h; have hp:= charge_sq; rw [h,zero_mul, eq_neg_iff_add_eq_zero] at hp; simp at hp
lemma wood (M : Spikeˣ) (h:KeepsC M) : M.val.transpose * C *M.val=C:=by
   let B:= M⁻¹.val; let A:= M.val; have he:B*A=1:= M.inv_val; have hx:A*B=1:= M.val_inv; have hp:B*C* (-C) = B:=by rw [mul_assoc, mul_neg,charge_sq, neg_neg,mul_one]
   have hk : C*A.transpose=B*C:=by rw [show B*C=B*(A*C*A.transpose) from (congr_arg (B*·) (show A*C*A.transpose=C from h).symm),←mul_assoc B,←mul_assoc, he,one_mul]

   have hA : A.transpose= -C*(B*C):=by rw [←hk,← mul_assoc, neg_mul,charge_sq,neg_neg,one_mul]
   change A.transpose*C*A=_; rw [hA,Matrix.mul_assoc ( -C) (B*C), mul_assoc B C, charge_sq,mul_neg,mul_one,neg_mul_neg, mul_assoc,he,mul_one]
lemma keeps_star (S:Spikeˣ)(h:KeepsC S) : KeepsC (star S):=by
   have he:= congr_arg star (wood S h); rw [star_mul,star_mul, star_charge] at he; unfold KeepsC; change star S.val*C*(star S.val).transpose=C; have hF: star S.val*((-C)* (star S.val).transpose)= -C:=he; exact neg_injective (by rwa [mul_assoc,← mul_neg, ← neg_mul] -- convert
   )

lemma lineP (X:Spikeˣ)(h:KeepsC X)(he:∀ i, Commute X.val (gamma i)): X=(1:Spikeˣ) ∨ X=-1:=by
    let c:=X.val (0,0) (0,0); have hX: X.val = c • 1:= Revolve.scalar_spin he
    have hp:c*c=1:=by
       have he:=h; unfold KeepsC at he; change X.val*C*X.val.transpose=C at he; rw [hX,transpose_smul,transpose_one,Matrix.smul_mul, Matrix.mul_smul,one_mul,mul_one,smul_smul] at he; apply smul_left_injective ℂ Cunit_ne; exact he.trans (one_smul ℂ C).symm -- order
    rcases mul_self_eq_one_iff.mp hp with hl|hl
    · left; exact Units.ext (by rw [Units.val_one]; rw [hl,one_smul] at hX; exact hX)
    right; apply Units.ext; change X.val= -1; rw [hX,hl,neg_one_smul]

lemma sensing (a : Axis) : slash (basis a)=gamma a:=by unfold slash; simp [basis]
lemma shines (x:E4): star (slash x)=slash x:=by unfold slash; simp
lemma coversK (X:Spikeˣ)(h: KeepsC X)(R:Ortho)(hp:∀ i, X.val*gamma i= slash (Ortho.move R (basis i))* X.val): X.val∈ _root_.unitary Spike:=by
    have he(i): Commute (star X.val * X.val) (gamma i):=by
       have ht:= congr_arg star (hp i); rw [star_mul,star_mul,gamma_star,shines] at ht
       unfold Commute SemiconjBy; rw [mul_assoc, hp i,← mul_assoc (star X.val), ← ht, mul_assoc]
    rcases lineP (star X * X) ((keeps_star X h).mul h) he with ht|ht
    · apply Matrix.mem_unitaryGroup_iff'.mpr; exact congr_arg Units.val ht
    exfalso; let i:Pinor:=(0,0); have hf : 0 ≤ (star X.val*X.val) i i:= (Matrix.posSemidef_conjTranspose_mul_self X.val).diag_nonneg -- check
    have h': star X.val*X.val= -1:=congr_arg Units.val ht; rw [h'] at hf; simp at hf; exact (not_le_of_gt (zero_lt_one' ℂ)) hf
end YM.Massive.Clifford
namespace YM.Massive.EuPin
open QCD QCD.Lat Lattice Wilson Mink Lorentz Function Matrix QCD.Revolve
open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology Kronecker ComplexOrder
open Clifford
variable (p:EuPin)
lemma act_gamma (j:Axis): p.matrix.val*gamma j= slash (Ortho.move p.coord (basis j))*p.matrix.val:=by have he := ((euPin_iff _).mp p.property).2 (basis j); rw [sensing] at he; exact he
lemma keeps : KeepsC p.matrix:= ((euPin_iff _).mp p.property).1
lemma isUnitary : p.matrix.val ∈ unitary _:= coversK p.matrix p.keeps p.coord p.act_gamma
lemma needed(q:EuPin)(he:p.coord=q.coord): p=q ∨ p.matrix= -q.matrix:=by
    let r:= q⁻¹ * p; have hp: r.coord=1:= by change q.coord⁻¹ * p.coord= _; rw [he,inv_mul_cancel]
    rcases lineP r.matrix r.keeps (fun i=> show _ from ((by unfold Commute SemiconjBy; rw [r.act_gamma,hp,Ortho.move_one,sensing]) : _ )) with h|h -- Eq defeq
    · left; apply Subtype.ext; apply Prod.ext he; change p.matrix=q.matrix; change q.matrix⁻¹ * p.matrix=1 at h; exact (inv_mul_eq_one.mp h).symm -- sym?
    right; change q.matrix⁻¹*p.matrix = -1 at h; rw [← mul_inv_cancel_left q.matrix p.matrix, h, mul_neg, mul_one]
lemma both : ∃ q:EuPin,p.coord=q.coord ∧ q.matrix= -p.matrix:=by
    let Q:= -p.matrix; have h:EuPin.coord p=p.coord:=rfl
    have hp: KeepsC Q:=by unfold KeepsC Q; simp [show p.matrix.val* C*p.matrix.val.transpose=C from keeps p] -- C name
    have he: (p.coord,Q)∈euPinSubgroup:=by rw [euPin_iff]; refine ⟨hp,fun i=> ?_⟩; change (-p.matrix.val)*_=_*(-p.matrix.val); rw [neg_mul,mul_neg, show p.matrix.val*_=_ from ((euPin_iff _).mp p.property).2 i]; rfl
    exact ⟨⟨(p.coord,Q),he⟩,rfl,rfl⟩
end YM.Massive.EuPin
#print axioms YM.Massive.EuPin.isUnitary
