import YM.QCD.Nola.Stall
import YM.QCD.Step.Wrapper
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset Kit
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff Matrix
variable {ι κ A B:Type*} {n : Side} {m:ℕ} [Fintype A][Fintype B]{s t a χ δ v C H η b:ℝ}
open Kites Pads Creek.Ledge
lemma pears (Y:Matrix A A ℂ)(f:Pairs A↪B)(x:Dirac A): birth (pond f Y) (Grass.embed f x)=Grass.embed f (fade Y x):=by
     let e:=Grass.embed f; let M:=pond (Embedding.refl _) Y; have hz(x:Dirac A):pond f Y (e x)= e (M x):=by
            have hp i z: Creek.v (f i) (e z)=e (Creek.v i z):=survives f.injective i z
            unfold M pond; simp only [ContinuousLinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
            change Y i j • Creek.v _ (Creek.v _ (e x)) = e (Y i j • Creek.v _ (Creek.v _ x)); rw [show Creek.v (pet f i) _=_ from hp (.inl i) x,show Creek.v (met f j) _= _ from hp (.inr j) _,map_smul]; rfl
     have ht(n:ℕ): (pond f Y ^ n : EndA B) (e x)= e ((M^n : EndA (Pairs A)) x):=by
          induction n with
          | zero=>simp
          | succ n ih=> rw [pow_succ',pow_succ']; change (pond f Y) ((pond f Y ^ n : EndA B) (e x))=_; rw [ih,hz]; rfl
     let T:= Stays.birther (pond f Y) (e x); have hA:= ((Stays.birther M x).mapL e.toLinearMap.toContinuousLinearMap); apply HasSum.unique T (hA.congr_fun ?_)
     intro i; change (i.factorial:ℂ)⁻¹ • ((pond f Y)^i: EndA B) (e x) =e ((i.factorial:ℂ)⁻¹ • ((M^i: EndA (Pairs A)) x)); rw [ht,map_smul]
lemma kindles (Y:Matrix A A ℂ)(X:Matrix B A ℂ)(W:Dirac A)
   (hh:IsUnit (Y+Xᴴ*X).det): let H:=Y+Xᴴ*X; sheath 1 X (gauss Y*W)= H.det • (adapter (H⁻¹*Xᴴ) (X*H⁻¹).transpose (fade H⁻¹ W)*gauss (1-X*H⁻¹*Xᴴ)):=by
    intro H; let T:= bladesF (H⁻¹*Xᴴ) (X*H⁻¹); rw [clothe]; simp only [Complex.ofReal_one, inv_one,one_pow,one_smul, joinD, neg_smul]; rw [asset _ hh _ _ T]; simp only [Matrix.neg_mul,Matrix.mul_neg,neg_neg]; change _ • (wipe A B T (birth (bark (T-T)) (birth (pond (head A B) H⁻¹) (embed (head A B) W)))*_)=_; rw [sub_self,show bark (0:Matrix (Pairs A) (Pairs B) ℂ)=0 from ?_,pears]; swap; · apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _; exact zero_smul ℂ (l (tail A B j)*Creek.v (head A B i))
    rw [show birth (0:EndA (Pairs (A⊕B))) = 1 from NormedSpace.exp_zero]; let S:= (wipe A B T).comp (embed (head A B)); suffices hv:S=adapter (H⁻¹*Xᴴ) (X*H⁻¹).transpose by change _ • (S _*_)=_; rw [hv]
    refine ext_atoms fun i=>?_ ; change wipe _ _ _ (embed _ (atom i))=changeVars _ (atom i); rw [embed_atom,wiper,change_atom]; rfl
lemma kinder (Y:Matrix A A ℂ)(Q: Matrix B A ℂ)(X Z:Patio (Pairs A)) (h:IsUnit (Y+Qᴴ*Q).det)(he: fade (Y+Qᴴ*Q)⁻¹ (exp X.val)=exp Z.val): let H:=Y+Qᴴ*Q; let F:=1-Q*H⁻¹*Qᴴ; sheath 1 Q (gauss Y* exp X.val)= H.det • (gauss F * exp (adapter (H⁻¹*Qᴴ) (Q*H⁻¹).transpose Z.val)):=by intro H F; rw [kindles _ _ _ h]; rw [he,map_weight]; exact congr_arg _ ((gauss_plus _).central _).eq
end YM.QCD.Nola
