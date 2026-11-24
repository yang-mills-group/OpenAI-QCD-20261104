import YM.Cardinal.Radome
import YM.Elms.Ideal
/-!
# Weighted algebra over arbitrary pre-shell labels and finite cap; no spin-charge restriction
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans
open scoped Topology BigOperators TensorProduct Pointwise Classical
abbrev Mini (d:ℕ):= ↥(cap d)
variable {d:ℕ}
noncomputable def setas (d:ℕ): Pol d →ₗ[ℂ] Mini d:= (drips d).codRestrict (cap d) drips_in
lemma toMini (p:Mini d) : setas d p.val=p:=Subtype.ext (drips_identity _ p.property)
lemma mulDry_left (d k:ℕ)(p q:Pol d): drips k (drips k p*q)=drips k (p*q):=by
   have hz(a b:PowerPair d) : drips k (drips k (gen a)*gen b)=drips k (gen a*gen b):=by
       rw [drips_gen]; split; · rfl
       next h=>
       rw [zero_mul,map_zero,gen,gen,Algebra.TensorProduct.tmul_mul_tmul]; by_cases he: Disjoint a.2 b.2
       · let c:PowerPair d:=(a.1+b.1,(a.2.disjUnion b.2 he)); have hc: UV.weight c=UV.weight a+UV.weight b:=by unfold UV.weight Labels.height c; rw [Finset.disjUnion_eq_union,Finset.sum_union he]; dsimp only; rw [map_add]; omega
         have hv:drips k (gen c)=0:=by rw [drips_gen,if_neg (by omega)]
         rw [MvPolynomial.monomial_mul,mul_one]; rcases mono_mul_sign _ _ he with H|H <;> rw [H]; exact hv.symm; rw [tmul_neg,map_neg]; change 0=-(drips k (gen c)); rw [hv,neg_zero]
       rw [mono_mul_zero _ _ he,tmul_zero,map_zero]
   rw [← (zBasis d).linearCombination_repr p,← (zBasis d).linearCombination_repr q]
   simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Finset.mul_sum,_root_.smul_mul_assoc,_root_.mul_smul_comm, map_sum,map_smul,minted,hz] -- order simpl
lemma mulDry_right (d k:ℕ)(p q:Pol d): drips k (p*drips k q)=drips k (p*q):=by
   have hz(a b:PowerPair d) : drips k (gen a*drips k (gen b))=drips k (gen a*gen b):=by
       rw [drips_gen]; split; · rfl
       next h=>
       rw [mul_zero,map_zero,gen,gen,Algebra.TensorProduct.tmul_mul_tmul]; by_cases he: Disjoint a.2 b.2
       · let c:PowerPair d:=(a.1+b.1,(a.2.disjUnion b.2 he)); have hc: UV.weight c=UV.weight a+UV.weight b:=by unfold UV.weight Labels.height c; rw [Finset.disjUnion_eq_union,Finset.sum_union he]; dsimp only; rw [map_add]; omega
         have hv:drips k (gen c)=0:=by rw [drips_gen,if_neg (by omega)]
         rw [MvPolynomial.monomial_mul,mul_one]; rcases mono_mul_sign _ _ he with H|H <;> rw [H]; exact hv.symm; rw [tmul_neg,map_neg]; change 0=-(drips k (gen c)); rw [hv,neg_zero]
       rw [mono_mul_zero _ _ he,tmul_zero,map_zero]
   rw [← (zBasis d).linearCombination_repr p,← (zBasis d).linearCombination_repr q]; simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Finset.mul_sum,_root_.smul_mul_assoc,_root_.mul_smul_comm, map_sum,map_smul,minted,hz]
-- flags.Real.Instance not inherit Tensor structure on whole infinite.P
local instance freeM(d:ℕ): Module.Free ℂ (Mini d):=Module.Free.of_divisionRing ℂ (Mini d)
noncomputable def inches (d:ℕ): Mini d ≃ₗ[ℂ](Fin (Module.finrank ℂ (Mini d))→ℂ):= (Module.finBasis ℂ (Mini d)).equivFun
noncomputable scoped instance normM (d:ℕ): NormedAddCommGroup (Mini d):= NormedAddCommGroup.induced _ _ _ (inches d).injective
noncomputable scoped instance posM (d:ℕ): NormedSpace ℂ (Mini d):= NormedSpace.induced _ _ _ (inches d)
noncomputable scoped instance cotM (d:ℕ) : CompleteSpace (Mini d):= FiniteDimensional.complete ℂ _
abbrev passport (d:ℕ): Label d →ₗ[ℂ] Mini d:= Submodule.inclusion (p:=labels d) (p':=cap d) inf_le_left
lemma travel (p:Label d): passport d p=setas d p.val:=by exact (toMini (passport d p)).symm
variable (J:Labels.Jet su)
lemma ready_at (p q:Pol d): ready d J (p*q)=ready d J p*ready d J q:=by
   induction p using TensorProduct.induction_on with
   | zero=> simp
   | add p q hp hq=> rw [add_mul,map_add,map_add,add_mul,hp,hq]
   | tmul p u=> induction q using TensorProduct.induction_on with
      | zero=>simp
      | add p q hp hq=>rw [mul_add,map_add,map_add,mul_add,hp,hq]
      | tmul q v=>rw [Algebra.TensorProduct.tmul_mul_tmul,ready_t,ready_t,ready_t,map_mul,_root_.smul_mul_assoc,_root_.mul_smul_comm,smul_smul]
lemma observe_prod (p q:Pol d)(t:ℝ): observation d J t (p*q)=observation d J t p*observation d J t q:=by
    simp only [observation,LinearMap.comp_apply,AlgHom.toLinearMap_apply,ready_at,map_mul]
noncomputable def pace (d:ℕ)(t:ℝ): Pol d→ₗ[ℂ] Pol d:= (zBasis d).constr ℂ fun p=> (t:ℂ)^ weight p • gen p
lemma pace_gen (p:PowerPair d) (t:ℝ): pace d t (gen p)=(t:ℂ)^ weight p • gen p:=by nth_rw 1 [← minted]; exact Module.Basis.constr_basis ..
lemma paced (p:Pol d)(t:ℝ) : ready d J (pace d t p) = observation d J t p:=by
   rw [← (zBasis d).linearCombination_repr p]; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,minted,pace_gen,gen_value,map_smul]
lemma race (t:ℝ)(p q:Pol d): pace d t (p*q)= pace d t p* pace d t q:=by apply Display.distinct; intro J; rw [ready_at,paced,paced,paced,observe_prod]
lemma directed (p:Pol d)(x t:ℝ) : observation d J x (pace d t p)=observation d J (t*x) p:=by
   rw [← (zBasis d).linearCombination_repr p]; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,minted,pace_gen,map_smul,gen_value,Complex.ofReal_mul, mul_pow,smul_smul]
lemma paceDry (p:Pol d)(t:ℝ)(k:ℕ): drips k (pace d t p)= pace d t (drips k p):=by
    apply DFunLike.congr_fun (f:=(drips k).comp (pace d t)) (g:=(pace d t).comp (drips k)) ?_ p; apply (zBasis d).ext; intro i; rw [minted,LinearMap.comp_apply,LinearMap.comp_apply,drips_gen,pace_gen,map_smul,drips_gen]; split; exact (pace_gen ..).symm; rw [smul_zero,map_zero]
lemma paintDry (p:Pol d)(t:su.El)(k:ℕ): drips k (colorAct t p)= colorAct t (drips k p):= by simp_rw [drips,LinearMap.sum_apply,map_sum,luminousG]
lemma pacepaint (p:Pol d)(t:ℝ)(u:su.El): pace d t (colorAct u p)=colorAct u (pace d t p):=by apply Display.distinct; intro J; rw [visual,paced,paced,lamp_obs]
lemma pace_iter (p:Pol d)(t t':ℝ): pace d t (pace d t' p)=pace d (t'*t) p:=by apply Display.distinct; intro J; rw [paced,paced,directed]
lemma pace_launch (p:Pol d): pace d 1 p=p:=by apply Display.distinct; intro J; rw [paced,one_scene]
noncomputable def paceM (d:ℕ)(v:ℝ): Mini d →ₗ[ℂ] Mini d:= (setas d).comp ((pace d v).comp (cap d).subtype)
lemma pace_local (x:Mini d)(t:ℝ): (paceM d t x).val=pace d t x.val:=by change drips d (pace d t x.val)=_; rw [paceDry,drips_identity _ x.property]
lemma setas_pace (p: Pol d)(t:ℝ): paceM d t (setas d p) = setas d (pace d t p):= by apply Subtype.ext; rw [pace_local]; exact (paceDry p t d).symm
lemma tint_life (p:Mini d)(u:su.El)(t v:ℝ):∃ y:Mini d, y.val=colorAct u p.val:= ⟨⟨_,radiant_cap u p.property⟩,rfl⟩ -- unused
end YM.Massive.Elm
#print axioms YM.Massive.Elm.pace_launch
#print axioms YM.Massive.Elm.mulDry_left
#print axioms YM.Massive.Elm.mulDry_right
