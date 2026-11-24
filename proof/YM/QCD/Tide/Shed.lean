import YM.QCD.Tide.Frost
import YM.QCD.Step.Wrapper
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Function NormedSpace Finset Grass Creek Kit Matrix
open scoped BigOperators Matrix Topology Classical
variable {A B C M: Type*}[Fintype A][Fintype B][Fintype C][Fintype M]
variable [DecidableEq A][DecidableEq B]
noncomputable def furnace (Q:Matrix A B ℂ): Dirac A→ₗ[ℂ]Dirac B:= (adapter Q (Twist Q)).toLinearMap.comp (winter _).toLinearMap
noncomputable def foam (Q:Matrix A B ℂ):= Matrix.fromBlocks 1 (-Q) (-Qᴴ) (Qᴴ*Q)
lemma mingler (Q:Matrix A B ℂ)(x:Dirac A): marginal A B (gauss (foam Q)*near A B x)= furnace Q x:=by
   let T:= bladesF Q Qᴴ; let I:= (1:Matrix A A ℂ)
   rw [foam,asset _ (by simp) (-Q) (-Qᴴ) T]; simp only [show (1:Matrix A A ℂ)⁻¹=1 from by simp,Matrix.one_mul, Matrix.mul_one,neg_neg,T,Matrix.neg_mul,Matrix.mul_neg,neg_neg,sub_self, Matrix.det_one,one_smul]; have hh:(bark (0:Matrix (Pairs A) (Pairs B) ℂ))=0:=by apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _; exact zero_smul ℂ (l (tail A B j)*v (head A B i))
   rw [show gauss (0:Matrix B B ℂ) = 1 from by simp [gauss,form],mul_one,hh,birth,exp_zero]; change wipe A B T (whip (head A B) (embed (head A B) x))= _; rw [storms];
   let L:Dirac A→ₐ[ℂ]Dirac B:= (wipe A B T).comp (embed (head A B))
   suffices h:L=adapter Q (Twist Q) by change L (winter _ x)=_; rw [h]; rfl
   refine ext_atoms fun i=> ?_; change wipe A B T (embed _ (atom i))=changeVars _ (atom i); rw [embed_atom,wiper,change_atom]; rfl
omit [DecidableEq A][DecidableEq B] in
lemma circlesH (P:Matrix A A ℂ)(Q:Matrix B B ℂ)(E:A≃B)(h:∀ i j,P i j=Q (E i) (E j)):pass E (gauss P)=gauss Q:=by
    unfold gauss; rw [map_weight]; apply congr_arg
    unfold form; simp only [map_sum,map_smul,map_mul,pass_psi,pass_bar,h]; rw [← Equiv.sum_comp E (fun i=> ∑ j:B, Q i j • (psi j * bar i))]
    apply sum_congr rfl; intro i _; exact Equiv.sum_comp E (fun j=> Q (E i) j • (psi j * bar (E i)))
lemma swapsS (Q:Matrix A B ℂ) : let E:= Equiv.sumComm B A; pass E (gauss (joinD 1 Q 0))=gauss (foam Q):=by
   intro E; apply circlesH; intro i j; cases i <;> cases j <;> simp [E,joinD,foam]
lemma ship (Q:Matrix A B ℂ)(x:Dirac B)(y:Dirac A):
   -- note argument order: gives y BEFORE source, no evenness fine when that convention
   Plus x → ber A (sheath 1 Q x*y)= ber B (x*furnace Q y):=by
   intro h
   let E:=Equiv.sumComm B A; let u:=pass E
   unfold sheath; simp only [Complex.ofReal_one,inv_one, one_pow,one_smul]
   rw [marginal_test, ← passed E, map_mul (pass E),map_mul (pass E),show pass E (gauss (joinD 1 Q 0))= _ from swapsS Q]
   have hz: u (near B A x)=far A B x:=AlgHom.congr_fun (pass_comp Sum.inl (⇑E)) x
   have he: u (far B A y)=near A B y:= AlgHom.congr_fun (pass_comp Sum.inr (⇑E)) y
   rw [show pass E (near B A x)=_ from hz,show pass E (far B A y)=_ from he,(h.central (furnace Q y)).symm.eq, ← mingler,marginal_test, mul_assoc, ((show Plus (far A B x) from (pass_grade ..).trans (congr_arg _ h)).central _).symm.eq]
lemma wP (i:A)(x:Dirac A):winter _ (psi i*x)=psi i*winter _ x+winter _ (vary (.inr i) x):= advanceP (Embedding.refl (Pairs A)) i x
lemma wM (i:A)(x:Dirac A):winter _ (bar i*x)=bar i*winter _ x- winter _ (vary (.inl i) x):= advanceM (Embedding.refl (Pairs A)) i x
-- product when disjoint and restriction at same time
noncomputable abbrev fuse (u:B↪ A): Pairs B ↪ Pairs A:= Embedding.sumMap u u
lemma halos (u:B↪ A)(i: Pairs B)(x: Dirac B): vary (fuse u i) (pass u x)=pass u (vary i x):= survives (fuse u).injective i x
lemma halo (u:B↪ A)(x:Dirac A)(hu:∀ i:Pairs B,vary (fuse u i) x=0)(y:Dirac B):
   winter _ (pass u y*x)=pass u (winter _ y)*winter _ x:=by
   let V:= LinearMap.mulRight ℂ x; let P: Dirac B →ₗ[ℂ] Dirac A:= ((winter A).toLinearMap.comp V).comp (pass u).toLinearMap; let T:= (LinearMap.mulRight ℂ (winter _ x)).comp ((pass u).toLinearMap.comp (winter _).toLinearMap)
   change P y=T y; apply LinearMap.congr_fun _ y
   refine story (f:=fuse u) (C:=atom) ⟨fun i y=>?_,fun i y=>?_⟩ ⟨fun i y=>?_,fun i y=>?_⟩ ?_
   · change winter _ (pass u (psi i*y)*x)=_; rw [map_mul (pass u),pass_psi,mul_assoc,wP,vary_mul,show vary (Sum.inr (u i)) x=0 from hu (.inr i),mul_zero,add_zero, show vary (Sum.inr (u i)) (pass u y)=_ from halos u (.inr i) y]; rfl
   · change winter _ (pass u (bar i*y)*x)=_; rw [map_mul (pass u),pass_bar,mul_assoc,wM,vary_mul,show vary (Sum.inl (u i)) x=0 from hu (.inl i),mul_zero,add_zero, show vary (Sum.inl (u i)) (pass u y)=_ from halos u (.inl i) y]; rfl
   · change pass u (winter _ (psi i*y))*_= _; rw [wP,map_add,map_mul,pass_psi,add_mul,mul_assoc]; rfl
   · change pass u (winter _ (bar i*y))*_= _; rw [wM,map_sub,map_mul,pass_bar,sub_mul,mul_assoc]; rfl
   change winter _ (pass u 1*x)=pass u (winter _ 1)*_; rw [show winter _ (1:Dirac B)=1 from cheers (Embedding.refl (Pairs B)),map_one,one_mul,one_mul]
lemma frosted (u:B↪ A)(y:Dirac B):winter A (pass u y)=pass u (winter _ y):=by
   have hh:= halo u (1:Dirac A) (fun i=> vary_one _) y; simpa [winter,cheers] using hh
-- orthogonal disjoint cross
lemma disjointH (u:B↪ A)(v:C↪ A)(hu:∀ i j,u i≠ v j)(x:Dirac B)(y:Dirac C): winter _ (pass u x*pass v y)= winter _ (pass u x)*winter _ (pass v y):=by
   rw [frosted]; apply halo; intro i
   have hh(i:Pairs B)(j:Pairs C):fuse u i≠ fuse v j:=by cases i <;> cases j <;> simp [fuse,hu]
   rcases i with i|i
   · exact ranger (fuse u) (fuse v) hh (.inl i) i y 0
   exact ranger (fuse u) (fuse v) hh (.inr i) i y 0
omit [DecidableEq B] in
lemma conjures (u:B↪ A)(v:C↪ A)(hu:∀ i j,u i≠v j)(x:Dirac B)(y:Dirac C)(Q:Matrix A M ℂ):furnace Q (pass u x*pass v y)=furnace Q (pass u x)*furnace Q (pass v y):=by
    classical
    change adapter _ _ (winter A _)= _; rw [disjointH u v hu, map_mul]; rfl
end YM.QCD.Tide
