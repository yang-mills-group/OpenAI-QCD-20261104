import YM.Lyre.Shine
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free.Lyre
open Function Filter MeasureTheory Lattice Wilson QCD QCD.Lat TensorProduct QCD.Grass Analysis YM.Arise.Range YM.Arise.Count Matrix Finset
open scoped Topology BigOperators ContDiff TensorProduct Matrix Matrix.Norms.L2Operator Kronecker Classical
variable {d e n m:ℕ}(a:Axis) (p q:E4)
variable {I:Type}[Fintype I]
local notation "T"=> Ortho.motion (Signed.reflect a)
local notation "Ha"=> gamma a
section
variable {S:I→Type*}[∀ i,Fintype (S i)]
noncomputable def quadrant (i j:I)(Y:Matrix (Sigma S) (Sigma S) ℂ):= Y.submatrix (Sigma.mk i) (Sigma.mk j)
variable (i j:I)(P:∀ i,Matrix (S i) (S i) ℂ)(Y:Matrix (Sigma S) (Sigma S) ℂ)
lemma quadL: quadrant i j (blockDiagonal' P * Y)=P i*quadrant i j Y:=by
    apply Matrix.ext; intro x y
    unfold quadrant; simp only [submatrix_apply, Matrix.mul_apply,Fintype.sum_sigma]
    rw [sum_eq_single i]; simp_rw [blockDiagonal'_apply_eq]
    intro k _ hk; refine sum_eq_zero fun l _=> ?_; rw [blockDiagonal'_apply_ne P _ _ (Ne.symm hk),zero_mul]; simp -- layout
lemma quadR : quadrant i j (Y*(blockDiagonal' P).transpose)=quadrant i j Y * (P j).transpose:=by rw [← Matrix.transpose_transpose Y,← Matrix.transpose_mul, (show quadrant i j (blockDiagonal' P * Yᵀ)ᵀ=(quadrant j i (blockDiagonal' P*Yᵀ))ᵀ from rfl), quadL]; rw [Matrix.transpose_mul]; rfl
end
noncomputable def crossV (x:I→E4): I→ E4:= fun i=>p+T (x i)
variable (x:I→E4)(w:I→ℕ)
noncomputable def DawnH (a:Axis)(w:I→ℕ):Matrix (Arms w) (Arms w) ℂ:= blockDiagonal' (fun i=> eyeW (w i) a)
local notation "X"=> crossV a p x
omit [Fintype I] in
lemma cornerL(i j:I): quadrant i j (callS x w)= if x i=x j then 0 else Matrix.fromBlocks 0 (axisL (x i) (x j) (w i) (w j)) 0 0 :=by
   split_ifs with h <;> apply Matrix.ext <;> rintro (y|y) (z|z) <;> simp [quadrant,callS,h,axisL]
lemma pitchC : DawnH a w * callS X w * (DawnH a w).transpose = star (callS x w):=by
   apply Matrix.ext; intro i j
   let a0:=i.1; let b:=j.1; let A:=i.2; let B:=j.2; let V:=DawnH a w
   have hv : quadrant a0 b (V*callS X w*V.transpose)=(quadrant b a0 (callS x w)).conjTranspose:=by
        unfold V DawnH; rw [quadR, quadL]; by_cases he:x a0=x b
        · rw [cornerL,cornerL, if_pos he.symm, if_pos (show X a0=X b from (congr_arg (fun y=>p+T y) he))]; simp
        rw [cornerL,cornerL, if_neg (Ne.symm he), if_neg (show X a0≠X b from fun h=> he ((T).injective (add_left_cancel h)))]; unfold eyeW; rw [Matrix.fromBlocks_transpose]; simp only [fromBlocks_multiply,Matrix.zero_mul, Matrix.mul_zero,add_zero,zero_add, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.transpose_zero]; -- check
        unfold crossV; rw [oriented a (x a0) (x b) he]
   exact congrFun (congrFun hv A) B
lemma hamR (i:I)(g:SpinPol (w i)): ham I i w (aSpin _ a g)=changeVars (DawnH a w) (dagger (ham I i w g)):=by
   let U:=(ham I i w).toLinearMap.comp (aSpin (w i) a); let h:= dagger.comp (ham I i w).toLinearMap; let Z:=(changeVars (DawnH a w)).toLinearMap.comp h
   change U g=Z g; apply LinearMap.congr_fun _ g
   apply ext_reversing (fun x y=>by simp only [U,aSpin,LinearMap.comp_apply, AlgHom.toLinearMap_apply,dagger_mul,map_mul]) (fun x y=>by simp only [Z,h,LinearMap.comp_apply,AlgHom.toLinearMap_apply,map_mul,dagger_mul]) (by simp [U,Z,h,aSpin,dagger_one])
   intro x; simp only [U,aSpin,Z,h,LinearMap.comp_apply, AlgHom.toLinearMap_apply,dagger_atom,ham,embed_atom,change_atom,map_sum,map_smulₛₗ]
   rw [Fintype.sum_sigma,sum_eq_single i]; simp only [RingHom.id_apply,DawnH,blockDiagonal'_apply_eq]
   intro j _ hj; refine sum_eq_zero fun v _=> ?_; change Matrix.blockDiagonal' _ _ _ • _=_; simp_rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hj),zero_smul]; simp
lemma downL {U:Type}[Fintype U](Y: Alg (Arms w)): erg I (U:=U) X w (changeVars (DawnH a w) (dagger Y)) = dagger (erg I x w Y):=by
    unfold erg; rw [LinearMap.comp_apply, LinearMap.comp_apply]; simp only [AlgHom.toLinearMap_apply, ContinuousLinearMap.coe_coe]; rw [QCD.Anomaly.transfer, pitchC, QCD.Eden.cast_voice]; unfold Arise.Pair.offP; rw [dagger_change]; let Q:=dagger (Creek.birth (QCD.Anomaly.Wand (callS x w)) Y); rw[show Mstar (0:Matrix (Arms w) U ℂ)=0 from ?_, ← AlgHom.comp_apply, ← change_mul]; simp [Matrix.mul_zero]
    apply Matrix.ext; intro i j; simp [Mstar]
end YM.Massive.UV.Free.Lyre
#print axioms YM.Massive.UV.Free.Lyre.hamR
#print axioms YM.Massive.UV.Free.Lyre.downL
