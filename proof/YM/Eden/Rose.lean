import YM.Eden.Luma
/-! # thermal & reflection covariance. Include star of reversal.Even spin kernel convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eden
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range
open Finset YM.Bank Precision Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Kit QCD.Bloom QCD.Pine QCD.Grass
open Massive Massive.UV Patria Patria.Exposure Revolve TorusPCAC.Geometry TorusPCAC.Geometry.AxisB
variable {c f:Side}{N k m:ℕ}{I J:Type}[Fintype I][Fintype J]
noncomputable abbrev slab (P:Matrix I J ℂ): Matrix (Pairs I) (Pairs J) ℂ:=Matrix.fromBlocks P 0 0 (Mstar P)
lemma pairs_roll (X:Matrix I I ℂ)(A: Matrix I I ℂ)(h: A*X*star A=X): slab A*stamping X*(slab A).transpose=stamping X:=by unfold slab stamping; rw [mstar_sq, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]; simp [h]
variable (F:Train k)(hk:2≤ k)
local notation "S"=>stage F c
local notation "M"=>copies 6 S
local notation "Ω"=> Buzz.start c F 6
open Cylinder
lemma star_eu (p:EuPin): (star p.matrix.val)=p.matrix⁻¹.val:=by
       calc _ = star p.matrix.val*(p.matrix.val*p.matrix⁻¹.val):=by rw [show p.matrix.val*p.matrix⁻¹.val=1 from p.matrix.val_inv,mul_one]
            _ = _ := by rw [← mul_assoc,p.isUnitary.1,one_mul]
noncomputable abbrev PinWheel (c:Side)(s:Signed)(p:EuPin):= slab (Action.moved (n:=c) (F:=6) s p.matrix⁻¹.val)
lemma pinWheel (s:Signed)(p:EuPin) {N:Side} (v:Grid N)(F:Density N 6): (changeVars (PinWheel N s p)) (F (pull s 0 v))=Action.pin p s F v:=by unfold Action.pin PinWheel slab; rw [← star_eu,dir_sail,mstar_sq,star_star]; rfl
include hk
lemma psyche (s:Signed)(p:EuPin)(h:p.Lifts s) : PinWheel c s p * Ω * (PinWheel c s p).transpose=Ω:=by
     apply pairs_roll; change Action.moved _ _ * M*_ = M; rw [← star_eu, ← Patria.rotor, ← copies_star, ← copies_mul, ← copies_mul]; exact congr_arg _ (rollingS F hk _ s 0 (prism s) (smoke _) (EuPin.retains _ h))
noncomputable abbrev BannerV (c:Side)(v:Cover) := copies 6 (hues (wrap c v) 1 (heat v) 1)
lemma sash (v:Cover) : slab (BannerV c v) * Ω * (slab (BannerV c v)).transpose=Ω:=by refine pairs_roll M _ ?_; unfold BannerV; rw[← copies_star,← copies_mul,← copies_mul]; exact congr_arg _ (rollingS F hk (1:Spike) 1 _ (heat v) (TorusPCAC.Geometry.glares (n:=c) v) Swing.none)
noncomputable abbrev grame (c:Side)(u:su.El): Matrix (Pairs (Modes c 6)) (Pairs (Modes c 6)) ℂ := slab (Lat.rotates 6 (fun _:Site c=>u))
lemma vigil(u:su.El) : grame c u * Ω * (grame c u).transpose=Ω:=by
    apply pairs_roll; unfold Lat.rotates; change copies _ _ * M*_ = M; rw [← copies_star,←copies_mul,←copies_mul]; exact congr_arg (copies 6) (twist_board (c:=c) F hk u)
noncomputable abbrev flavP (c:Side)(u:FlavorTorus) : Matrix (Modes c 6) (Modes c 6) ℂ:= byFlavor u Prod.snd
omit hk
lemma flavorRoll(u:FlavorTorus) : slab (flavP c u) * Ω * (slab (flavP c u)).transpose=Ω:=by
    apply pairs_roll; ext i j; unfold flavP byFlavor; rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]; by_cases he:i.2=j.2 <;> simp [choir,Matrix.blockDiagonal_apply,he];
    let x:ℂ:= (u j.2).val; let y:ℂ:= Flume.stage F c i.1 j.1; change x*y*star x = y ; rw [mul_right_comm,show x * star x=1 from (u j.2).property.2,one_mul] -- replace
include hk
noncomputable abbrev moonS (c:Side)(a:Axis) : Matrix (Pairs (Modes c 6)) (Pairs (Modes c 6)) ℂ:= Matrix.fromBlocks 0 (Action.moved (Signed.mirror a) (-(gamma a).transpose)) (Action.moved (Signed.mirror a) (-gamma a)) 0
noncomputable abbrev railN (c:Side): Matrix (Pairs (Modes c 6)) (Pairs (Modes c 6)) ℂ:=Matrix.fromBlocks 0 (Action.moved 1 chargeMatrix) (Action.moved 1 (-(chargeMatrix⁻¹).transpose)) 0
variable (a:Axis)
lemma slight : moonS c a * Ω * (moonS c a).transpose= star Ω:=by
     let s:=Signed.mirror a; let E:=eyeP c a; let B:=M; have ht:= tilt_copy (c:=c) F hk a
     have he:E*B*E=star B:=by change E*star B*E=B at ht; nth_rw 1 [← ht]; simp only [mul_assoc]; rw [show E*E=1 from eye_sq _,mul_one,← mul_assoc,show E*E=1 from eye_sq _,one_mul]
     have h1:Action.moved s (-(gamma a).transpose) (n:=c) (F:=6)= -E.transpose:=by
         have hx : Mstar (eyeP c a)= E.transpose:=by rw[mstar_sq,eye_star]
         rw [eye_moved,←hx]; unfold eyeP; rw [dir_sail, mstar_sq,gamma_star]
     have hh:Action.moved s (-gamma a) (n:=c) (F:=6)= -E:=eye_moved ..
     rw [show moonS c a= fromBlocks 0 (-Eᵀ) (-E) 0 from (by unfold moonS; rw[h1,hh])]; change (fromBlocks _ _ _ _) * stamping B * _ᵀ = star (stamping B); unfold stamping; rw[fromBlocks_transpose,fromBlocks_multiply,fromBlocks_multiply,Matrix.star_eq_conjTranspose,fromBlocks_conjTranspose]; simp [he]; rfl
lemma raised : railN c * Ω *(railN c).transpose= -(Ω).transpose:=by
     let X := TorusPCAC.Jet.Cmat; let P:=copies 6 (onSpin c X); let Q:= copies 6 (onSpin c X⁻¹); have h : Pᵀ = -P:=by
        rw [show Pᵀ = _ from (show Pᵀ=Jobs c 6 Xᵀ from transpJob _ )]; rw [show Xᵀ=-X from Clifford.transpose_charge]; unfold Jobs; rw [opposite]; ext i j; by_cases he:i.2=j.2 <;> simp [copies,he, Matrix.blockDiagonal_apply,P]
     have he: Q= -P:=by
       rw [show Q= copies 6 (onSpin c (-X)) from ?_,opposite]; · ext i j; by_cases he:i.2=j.2 <;> simp [copies, Matrix.blockDiagonal_apply,P,he]
       unfold Q; rw [show X⁻¹= -X from ?_]; exact Matrix.inv_eq_right_inv (by rw [mul_neg, show X*X= -1 from Clifford.charge_sq, neg_neg]) -- scope
     let B:=M; have hf: (Q*B*P).transpose=B:=by unfold Q B P; rw [← copies_mul, ←copies_mul]; unfold copies; rw [Matrix.blockDiagonal_transpose]; exact congr_arg _ (funext fun _=>oppositeS F hk) -- transpose
     unfold railN; rw [show Action.moved 1 chargeMatrix (n:=c) (F:=6)=P from stillB _,Massive.UV.invertC,eye_moved,show Action.moved 1 chargeMatrix (n:=c) (F:=6)=P from stillB _] -- duplicate
     change (fromBlocks _ _ _ _)*stamping B*_ᵀ= -(stamping B)ᵀ; unfold stamping; rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, fromBlocks_transpose]; have H:= congr_arg transpose hf; rw [he,transpose_transpose] at H; simp only [transpose_zero,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,h,Matrix.mul_neg]; rw [H]; ext i j; cases i <;> cases j <;> simp

end YM.QCD.Eden
#print axioms YM.QCD.Eden.psyche
