import YM.Plateau.Curl
/-! # UV projected P/S-channel at pre-rotation plane. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b: Flavor 6)(g:Bool)
open Poised.Display Poised.Stative Module Finset Revolve UV.Free
local notation "P"=>Pairs (SpinMode 8)
local notation "Θ"=>thetaBasis P
local notation "q"=> slashEq 8
local notation "X" => ExteriorAlgebra ℂ (Seed P ⧸ q)
set_option quotPrecheck false
local notation "E"=> ExteriorAlgebra.map ((q).mkQ)
private lemma paying (u:Axis): UV.Free.AtNext u (0:Multi 8) (UV.first u):=by
     funext j; rw [nectar]; by_cases h:j=u; subst j; rw[Function.update_self]; simp; rfl -- check rfl
     rw [Function.update_of_ne h,if_neg (Ne.symm h)]; rfl
private lemma dawn (u:Axis) (v:Multi 8): UV.Free.AtNext u 0 v ↔ v=UV.first u:=by
    constructor; · intro h; exact Subtype.ext (funext fun j=> Fin.ext (congr_fun (h.trans (paying u).symm) j))
    rintro rfl; exact paying u
noncomputable abbrev bLine (a:Flavor 6) (p:Multi 8)(i:Pinor)(j:Hue):X := (E) (bar ((p,i,j),a))
noncomputable abbrev cLine (a:Flavor 6) (p:Multi 8)(i:Pinor)(j:Hue):X := (E) (psi ((p,i,j),a))
lemma ash(i:Pinor)(k:Hue): ∑ u:Axis, ∑ t:Pinor, gamma u t i • bLine a (UV.first u) t k=0:=by
    let W:SpinMode 8:= ((0,i,k),a); let V:= slashBar W; have h: (q).mkQ V=0:= (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inr ⟨_,rfl⟩)); -- implicit
    have hh : V=∑ u:Axis,∑ s:Pinor, gamma u s i • Θ (Sum.inr ((UV.first u,s,k),a)):=by unfold V slashBar W; simp [dawn]
    rw [hh] at h; have hp:= congr_arg (ExteriorAlgebra.ι ℂ) h; simp_rw [map_sum,map_smul,map_zero] at hp; apply Eq.trans (?_: _=_) hp
    unfold bLine bar atom; simp_rw [ExteriorAlgebra.map_apply_ι]
lemma pine(i:Pinor)(k:Hue): ∑ u:Axis,∑ t:Pinor, gamma u i t • cLine a (UV.first u) t k=0:=by
    let W:SpinMode 8:= ((0,i,k),a); let V:= slashCol W; have h:(q).mkQ V=0:=(Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inl ⟨_,rfl⟩));
    have hh : V=∑ u:Axis,∑ t:Pinor,gamma u i t • Θ (Sum.inl ((UV.first u,t,k),a)):=by unfold V slashCol W; simp [dawn]
    rw [hh] at h; have hp:= congr_arg (ExteriorAlgebra.ι ℂ) h; simp_rw [map_sum,map_smul,map_zero] at hp; apply Eq.trans (?_: _=_) hp
    unfold cLine psi atom; simp_rw [ExteriorAlgebra.map_apply_ι]
local notation "B"=>bLine a
local notation "C"=>cLine b
lemma lossL (S:Spike): ∑ u:Axis,∑ i:Pinor,∑ j:Pinor,∑ k:Hue,(gamma u*S) i j • (B (UV.first u) i k*C 0 j k)=0:=by
    have h (j:Pinor)(k:Hue)(p:Pinor):∑ u:Axis,∑ i:Pinor,(gamma u i p*S p j) •(B (UV.first u) i k*C 0 j k)=0:=by
        rw [show (0:X)= S p j • ((∑ u:Axis, ∑ i:Pinor, gamma u i p • B (UV.first u) i k)*C 0 j k) from (by rw[ash,zero_mul,smul_zero]),Finset.sum_mul,Finset.smul_sum]; refine sum_congr rfl (fun u _=>?_); rw [Finset.sum_mul,Finset.smul_sum]; refine sum_congr rfl (fun i _=>?_); rw [_root_.smul_mul_assoc,smul_smul,mul_comm (S p j)]
    have hh {I J K O P':Type}[Fintype I][Fintype J][Fintype K][Fintype O][Fintype P'] (f:I→J→K→O→P'→X): ∑ i,∑ j, ∑ k,∑ o,∑ p,f i j k o p=∑ k,∑ o,∑ p,∑ i,∑ j,f i j k o p:=by
         conv_lhs=> arg 2; intro i; rw [sum_comm]; arg 2; intro k; rw [sum_comm]; arg 2; intro o; rw [sum_comm]
         rw[sum_comm]; refine sum_congr rfl fun k _=>?_ ; rw [sum_comm]; refine sum_congr rfl fun o _=>?_ ; rw [sum_comm]
    simp_rw[Matrix.mul_apply,sum_smul]; rw [hh (fun (u:Axis)(i j:Pinor)(k:Hue)(p:Pinor)=> (gamma u i p*S p j) •(B (UV.first u) i k*C 0 j k))]; simp_rw [h,sum_const_zero]
lemma lossR (S:Spike): ∑ u:Axis,∑ i:Pinor,∑ j:Pinor,∑ k:Hue,(S*gamma u) i j • (B 0 i k*C (UV.first u) j k)=0:=by
    have h(i:Pinor)(k:Hue)(p:Pinor): ∑ u:Axis,∑ j:Pinor,(S i p*gamma u p j) • (B 0 i k*C (UV.first u) j k)=0:=by
        rw [show (0:X)=S i p • ((B 0 i k)*∑ u:Axis,∑ j:Pinor,gamma u p j • C (UV.first u) j k) from (by rw[pine,mul_zero,smul_zero]),Finset.mul_sum,Finset.smul_sum]; refine sum_congr rfl fun u _=>?_; rw[Finset.mul_sum,Finset.smul_sum]; refine sum_congr rfl fun j _=>?_; rw [_root_.mul_smul_comm,smul_smul]
    have hh {I J K O P':Type}[Fintype I][Fintype J][Fintype K][Fintype O][Fintype P'] (f:I→J→K→O→P'→X): ∑ i,∑ k, ∑ j,∑ o,∑ p,f i j k o p=∑ k,∑ o,∑ p,∑ i,∑ j,f i j k o p:=by
         rw [sum_comm]; refine sum_congr rfl fun k _=>?_
         conv_lhs=> arg 2; intro i; rw [sum_comm]; arg 2; intro o; rw[sum_comm]
         rw[sum_comm]; refine sum_congr rfl fun o _=>?_ ; rw [sum_comm]
    simp_rw[Matrix.mul_apply,sum_smul]; rw [hh (fun (u:Axis)(j i:Pinor)(k:Hue)(p:Pinor)=> (S i p*gamma u p j) • (B 0 i k*C (UV.first u) j k))]; simp_rw[h,sum_const_zero]
lemma flipK(i:Axis): claw g i=(-poli g • (pulp g))*gamma i:=by cases g <;> simp [poli, claw,pulp] ; rw[Lat.five] -- inspect
set_option maxHeartbeats 670000 in
lemma projection_void (p:Bool):UV.Free.projection (arbor a b g p)=0:=by
     apply Subtype.ext; change UV.Free.reduceEq (arbor a b g p).val=0; rw [arbola,map_sum]; unfold bilinear UV.Free.reduceEq; simp_rw [TensorProduct.map_tmul,AlgHom.toLinearMap_apply,map_sum,map_smul,map_mul]; rw [←TensorProduct.tmul_sum]; cases p; -- simplify
     · simp_rw [flipK]; change _ ⊗ₜ[ℂ] (∑ u:Axis,∑ i:Pinor,∑ j:Pinor,∑ k:Hue,((-poli g • (pulp g))*gamma u) i j • (B 0 i k*C (UV.first u) j k)) = _; rw [show (∑ u:Axis,∑ i:Pinor,∑ j:Pinor,∑ k:Hue,((-poli g • (pulp g))*gamma u) i j • (B 0 i k*C (UV.first u) j k))=0 from lossR a b _] -- need change exact
       exact TensorProduct.tmul_zero ..
     change _ ⊗ₜ[ℂ] (∑ u:Axis,∑ i:Pinor,∑ j:Pinor,∑ k:Hue,(gamma u*pulp g) i j • (B (UV.first u) i k*C 0 j k))=_; rw [lossL,TensorProduct.tmul_zero]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.projection_void
