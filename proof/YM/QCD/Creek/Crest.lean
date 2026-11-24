import YM.QCD.Creek.Vale
/-! # Budget-priced evaluator skeleton at pinned H
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Grass NormedSpace Function Finset
open scoped Topology BigOperators Matrix
variable {A B M:Type*} [Fintype A][Fintype B][Fintype M]
variable (f:Pairs A ↪ M) (z:B ↪ M) (hZ : ∀ i j,f i ≠ z j) (V:Matrix A A ℂ)
variable [DecidableEq A][DecidableEq B]
lemma meadow (x: Alg (Pairs B)) (K:Matrix (Pairs A) (Pairs B) ℂ) : wipe A B K (far A B x)=x:=by
   let C: Dirac B →ₐ[ℂ] Dirac B:= (wipe A B K).comp (far A B)
   have hv: C=AlgHom.id ℂ _:= ext_atoms fun i=>by change wipe A B K (embed _ _) = atom i; rw [embed_atom]; exact tails A B K _
   change C x=x; rw [hv]; rfl

lemma room (H:Matrix A A ℂ)(hu:IsUnit H.det)(x:Dirac (A⊕B)): marginal A B (near A B (gauss H)* x)= H.det • wipe A B 0 (birth (pond (head A B) H⁻¹) x):=by
    let T:= birth (pond (head A B) H⁻¹)
    have hh : ∀ X:Dirac (A⊕B), marginal A B (near A B (gauss H)* X)= H.det • wipe A B 0 (T X):=by
      intro X
      have hp (x:Dirac A) (y:Dirac B): marginal A B (near A B (gauss H)*(near A B x*far A B y)) = H.det • wipe A B 0 (T (near A B x*far A B y)):=by
        have hv:= roundP ((accum (head A B) (tail A B) (heights A B) H⁻¹ y).symm)
        rw [← mul_assoc,← map_mul,margins,show T (near A B x*far A B y)= T (near A B x)*far A B y from DFunLike.congr_fun hv.symm.eq (near A B x),map_mul (wipe A B 0),meadow, show wipe A B 0 (T (near A B x))=seen H x • 1 from drained (B:=B) H hu x]; rw [seen_apply,smul_mul_assoc,one_mul,smul_smul,← mul_assoc,mul_inv_cancel₀ hu.ne_zero,one_mul]
      rw [← write X,mul_sum,map_sum,map_sum,map_sum,smul_sum]; apply sum_congr rfl; intro i _; obtain ⟨x,y,h|h⟩:=split_mono A B i <;> simp only [h,mul_smul_comm,map_smul,mul_neg,map_neg,hp] <;> rw [smul_comm] <;> simp
    exact hh x
lemma asset (H:Matrix A A ℂ)(hu:IsUnit H.det)(P:Matrix A B ℂ)(Q:Matrix B A ℂ)(X:Matrix (Pairs A) (Pairs B) ℂ)(x:Dirac (A⊕B)) (W:Matrix B B ℂ): marginal A B (gauss (Matrix.fromBlocks H P Q W)* x)= H.det • (wipe A B X (birth (bark (bladesF (-(H⁻¹*P)) (-(Q*H⁻¹))- X)) (birth (pond (head A B) H⁻¹) x))*gauss (W-Q*H⁻¹*P)):=by
   let D:= bladesF (-(H⁻¹*P)) (-(Q*H⁻¹))
   let E:=pond (head A B) H⁻¹
   let K:= bark D
   have hp: Commute (birth E) (birth K):= roundP ((roundP (pondB H⁻¹ D).symm).symm)
   rw [push _ P Q _ hu, room _ hu,smul_mul_assoc]; congr 2
   rw [show shear _ _ x = birth K x from congr_arg (fun M:EndA (Pairs (A⊕B))=>M x) (shear_equals _ _), show birth E (birth K x)= birth K (birth E x) from DFunLike.congr_fun hp.eq x]
   change wipe A B 0 (birth (bark D) _) = wipe A B X (birth (bark (D-X)) _)
   rw [skinny,skinny,zero_add,add_sub_cancel]
end YM.QCD.Creek
