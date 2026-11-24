import YM.Tawny.Eos
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)

namespace Dream
open TableT Carnal Rays Perla Zinc Grass Matrix
local notation "Ψ"=>SpinMode d
local notation "P"=> Pairs (SpinMode d)
local notation "Q"=>slashEq d
local notation "X" => ExteriorAlgebra ℂ (Seed P ⧸ Q)
set_option quotPrecheck false
local notation "E"=> ExteriorAlgebra.map ((Q).mkQ)
local notation "Θ"=>thetaBasis (Pairs (SpinMode d))
noncomputable abbrev dowC (d:ℕ):=ExteriorAlgebra.map ((slashEq d).mkQ)
noncomputable def c0(a:Flavor 6)(p:Multi d)(i:Pinor)(j:Hue):= (dowC d) (psi ((p,i,j),a))
noncomputable def b0(a:Flavor 6)(p:Multi d)(i:Pinor)(j:Hue):= (dowC d) (bar ((p,i,j),a))
namespace Quot
variable (v y:Multi d)(f:Axis→Multi d)(h:∀ i,AtNext i v (f i))
include h
lemma f_n(i:Axis)(k:Multi d) : AtNext i v k ↔ k=f i:=⟨fun H=> via_eq k _ (H.trans (h i).symm),fun t=> t.symm ▸ h i⟩
lemma ash(i:Pinor)(k:Hue): ∑ u:Axis, ∑ t:Pinor, gamma u t i • b0 a (f u) t k=0:=by
    let W:SpinMode d:= ((v,i,k),a); let V:= slashBar W; have ht: (Q).mkQ V=0:= (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inr ⟨_,rfl⟩)); -- implicit
    have hh : V=∑ u:Axis,∑ s:Pinor, gamma u s i • Θ (Sum.inr ((f u,s,k),a)):=by unfold V slashBar W; simp [f_n v f h]
    rw [hh] at ht; have hp:= congr_arg (ExteriorAlgebra.ι ℂ) ht; simp_rw [map_sum,map_smul,map_zero] at hp; apply Eq.trans (?_: _=_) hp
    unfold b0 dowC bar atom; simp_rw [ExteriorAlgebra.map_apply_ι]
lemma pine(i:Pinor)(k:Hue): ∑ u:Axis,∑ t:Pinor, gamma u i t • c0 a (f u) t k=0:=by
    let W:SpinMode d:= ((v,i,k),a); let V:= slashCol W; have ht:(Q).mkQ V=0:=(Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inl ⟨_,rfl⟩));
    have hh : V=∑ u:Axis,∑ t:Pinor,gamma u i t • Θ (Sum.inl ((f u,t,k),a)):=by unfold V slashCol W; simp [f_n v f h]
    rw [hh] at ht; have hp:= congr_arg (ExteriorAlgebra.ι ℂ) ht; simp_rw [map_sum,map_smul,map_zero] at hp; apply Eq.trans (?_: _=_) hp
    unfold c0 dowC psi atom; simp_rw [ExteriorAlgebra.map_apply_ι]
local notation "B"=>b0 a
local notation "C"=>c0 b
lemma lossL (S:Spike): ∑ u:Axis,∑ i:Pinor,∑ j:Pinor,∑ k:Hue,(gamma u*S) i j • (B (f u) i k*C y j k)=0:=by
    have h (j:Pinor)(k:Hue)(p:Pinor):∑ u:Axis,∑ i:Pinor,(gamma u i p*S p j) •(B (f u) i k*C y j k)=0:=by
        rw [show (0:X)= S p j • ((∑ u:Axis, ∑ i:Pinor, gamma u i p • B (f u) i k)*C y j k) from (by rw[ash a v f h,zero_mul,smul_zero]),Finset.sum_mul,Finset.smul_sum]; refine sum_congr rfl (fun u _=>?_); rw [Finset.sum_mul,Finset.smul_sum]; refine sum_congr rfl (fun i _=>?_); rw [_root_.smul_mul_assoc,smul_smul,mul_comm (S p j)]
    have hh {I J K O P':Type}[Fintype I][Fintype J][Fintype K][Fintype O][Fintype P'] (f:I→J→K→O→P'→X): ∑ i,∑ j, ∑ k,∑ o,∑ p,f i j k o p=∑ k,∑ o,∑ p,∑ i,∑ j,f i j k o p:=by
         conv_lhs=> arg 2; intro i; rw [sum_comm]; arg 2; intro k; rw [sum_comm]; arg 2; intro o; rw [sum_comm]
         rw[sum_comm]; refine sum_congr rfl fun k _=>?_ ; rw [sum_comm]; refine sum_congr rfl fun o _=>?_ ; rw [sum_comm]
    simp_rw[Matrix.mul_apply,sum_smul]; rw [hh (fun (u:Axis)(i j:Pinor)(k:Hue)(p:Pinor)=> (gamma u i p*S p j) •(B (f u) i k*C y j k))]; simp_rw [h,sum_const_zero]
lemma lossR (S:Spike): ∑ u:Axis,∑ i:Pinor,∑ j:Pinor,∑ k:Hue,(S*gamma u) i j • (B y i k*C (f u) j k)=0:=by
    have h(i:Pinor)(k:Hue)(p:Pinor): ∑ u:Axis,∑ j:Pinor,(S i p*gamma u p j) • (B y i k*C (f u) j k)=0:=by
        rw [show (0:X)=S i p • ((B y i k)*∑ u:Axis,∑ j:Pinor,gamma u p j • C (f u) j k) from (by rw[pine b v f h,mul_zero,smul_zero]),Finset.mul_sum,Finset.smul_sum]; refine sum_congr rfl fun u _=>?_; rw[Finset.mul_sum,Finset.smul_sum]; refine sum_congr rfl fun j _=>?_; rw [_root_.mul_smul_comm,smul_smul]
    have hh {I J K O P':Type}[Fintype I][Fintype J][Fintype K][Fintype O][Fintype P'] (f:I→J→K→O→P'→X): ∑ i,∑ k, ∑ j,∑ o,∑ p,f i j k o p=∑ k,∑ o,∑ p,∑ i,∑ j,f i j k o p:=by
         rw [sum_comm]; refine sum_congr rfl fun k _=>?_
         conv_lhs=> arg 2; intro i; rw [sum_comm]; arg 2; intro o; rw[sum_comm]
         rw[sum_comm]; refine sum_congr rfl fun o _=>?_ ; rw [sum_comm]
    simp_rw[Matrix.mul_apply,sum_smul]; rw [hh (fun (u:Axis)(j i:Pinor)(k:Hue)(p:Pinor)=> (S i p*gamma u p j) • (B y i k*C (f u) j k))]; simp_rw[h,sum_const_zero]
lemma c_loss(S:Spike): reduceEq (∑ i:Axis,bilinear a b (S*gamma i) y (f i))=0:=by
     rw [_root_.map_sum]; unfold UV.Free.reduceEq bilinear; simp_rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,map_one,_root_.map_sum,_root_.map_smul,map_mul]; rw[← TensorProduct.tmul_sum]; exact Eq.trans (congr_arg (tmul ℂ (1:Maxwell.WickPol su)) (lossR a b v y f h S)) (TensorProduct.tmul_zero ..)
lemma b_loss (S:Spike): reduceEq (∑ i:Axis,bilinear a b (gamma i*S) (f i) y)=0:=by
     rw [_root_.map_sum]; unfold UV.Free.reduceEq bilinear; simp_rw [TensorProduct.map_tmul,AlgHom.toLinearMap_apply,map_one,_root_.map_sum,_root_.map_smul,map_mul]; rw[← TensorProduct.tmul_sum]; exact Eq.trans (congr_arg (tmul ℂ (1:Maxwell.WickPol su)) (lossL a b v y f h S)) (TensorProduct.tmul_zero ..)
end Quot
end Dream
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Dream.Quot.c_loss
