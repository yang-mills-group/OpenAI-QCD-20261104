import YM.Poised.Lamp
import YM.QCD.Creek.Cost
import YM.Massive.Target.Wick
/-!
# Tiered measuring on all Grass letters

No rank restriction; twice-engineering convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Beacon
variable {c : Side}{d : ℕ}
namespace Display
variable (H:TaperHol)(b : Cover)
def endor (v:ℝ): SpinPol d→ₐ[ℂ]SpinPol d:= Grass.adapter (scaled v) (scaled v)
def sky (x:Finset (Pairs (SpinMode d))):= ∑ i∈x,letterWeight i
lemma pieces (x:Finset (Pairs (SpinMode d))) (v:ℝ): endor v (mono x)=(v:ℂ)^sky x • mono x:= by
   unfold endor adapter; let f(i : Pairs (SpinMode d)):= v^letterWeight i; let M:= Matrix.diagonal (fun i=> (f i:ℂ))
   have ht: Matrix.fromBlocks (scaled (d:=d) v) 0 0 (scaled (d:=d) v) = M:=by
      ext (i|i) (j|j) <;> simp only [M,f,scaled,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.diagonal_apply] <;> by_cases he:i=j <;> simp [*,letterWeight] -- inspect
   rw [ht,show changeVars M (mono x)= _ from QCD.Creek.wscale_mono f x]; unfold sky f; simp_rw [Complex.ofReal_pow, Finset.prod_pow_eq_pow_sum]
abbrev zBasis(d:ℕ):= UV.Free.basisU d
lemma minted (p:PowerPair d): zBasis d p=gen p:=by unfold zBasis UV.Free.basisU; rcases p with ⟨a,b⟩; simp [gen,mono] -- simp
-- polynomial span induction easier use zBasis.constr
open TensorProduct
def geometry (k:ℕ):Pol d→ₗ[ℂ]Pol d:= (zBasis d).constr ℂ fun p=>if weight p=k then gen p else 0
def drips (k:ℕ):Pol d→ₗ[ℂ]Pol d:= ∑ i ∈Finset.range (k+1), geometry i
lemma geometry_basis (p:PowerPair d)(k:ℕ): geometry k (gen p)=if weight p=k then gen p else 0:=by nth_rw 1 [← minted p]; exact Module.Basis.constr_basis ..
lemma drips_gen (x:PowerPair d)(k:ℕ): drips k (gen x)=if weight x≤k then gen x else 0 := by unfold drips; rw [LinearMap.sum_apply]; simp_rw [geometry_basis]; simp [Nat.lt_add_one_iff]
lemma drips_geom (i k:ℕ) (x:Pol d)(h:i≤k) : geometry i (drips k x)=geometry i x:=by
   refine DFunLike.congr_fun (f:=(geometry i).comp (drips k)) (g:=geometry i) ?_ x; apply (zBasis d).ext; intro j; rw [minted,LinearMap.comp_apply,drips_gen]; split; rfl
   rename_i hQ; rw [geometry_basis, map_zero, if_neg (by omega)] -- order
lemma drips_in (x:Pol d): drips d x ∈ UV.cap d:=by
    -- basis induction
    let B:=zBasis d
    rw [← B.linearCombination_repr x]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,map_smul]; refine Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ _ ?_)
    unfold B; rw [minted,drips_gen]; split
    next h=> exact Submodule.subset_span ⟨_,h,rfl⟩
    next=> exact Submodule.zero_mem _
lemma drips_identity (x:Pol d)(h:x∈UV.cap d): drips d x=x:=by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h
    · rintro _ ⟨i,hi,rfl⟩; exact (drips_gen ..).trans (if_pos hi)
    · rw [map_zero]
    · intro a b _ _ ha hb; rw [map_add,ha,hb]
    intro z a _ ha; rw [map_smul,ha]
def ready (d:ℕ)(J:Labels.Jet su): Pol d→ₗ[ℂ]SpinPol d:= ((TensorProduct.lid ℂ (SpinPol d)).toLinearMap).comp (TensorProduct.map (Labels.read J).toLinearMap LinearMap.id)
lemma ready_t (J:Labels.Jet su)(x:GPol)(y:SpinPol d): ready d J (x ⊗ₜ[ℂ] y)=Labels.read J x • y:=by unfold ready; rw [LinearMap.comp_apply,TensorProduct.map_tmul,LinearEquiv.coe_coe,lid_tmul]; rfl
private lemma scale_m (J:Labels.Jet su)(m:Powers)(x:ℝ) : Labels.read (scaleJet J x) (MvPolynomial.monomial m 1)=(x:ℂ)^Labels.height m*Labels.read J (MvPolynomial.monomial m 1):=by
    simp only [Labels.read,MvPolynomial.aeval_monomial, Algebra.algebraMap_self,RingHom.id_apply,one_mul, Finsupp.prod]
    simp_rw [Next.Foundations.coord_scales,Complex.real_smul,Complex.ofReal_pow,mul_pow, Finset.prod_mul_distrib,← pow_mul]; congr 1; unfold Labels.height; rw [prod_pow_eq_pow_sum,Finsupp.weight_apply]; apply congr_arg; unfold Finsupp.sum; exact Finset.sum_congr rfl fun a _=>Nat.mul_comm ..
def observation (d:ℕ)(J:Labels.Jet su)(x:ℝ):Pol d→ₗ[ℂ]SpinPol d:= (endor x).toLinearMap.comp (ready d (scaleJet J (x^2)))
lemma observe (J:Labels.Jet su)(x:Pol d)(t:ℝ): observation d J t x=desired x J t:=by
   apply DFunLike.congr_fun (f:=observation d J t) (g:= (TensorProduct.lid ℂ _).toLinearMap.comp (TensorProduct.map (Labels.read (scaleJet J (t^2))).toLinearMap (endor t).toLinearMap)) _ x; apply TensorProduct.ext'; intro p q; rw [observation,LinearMap.comp_apply, LinearMap.comp_apply,LinearEquiv.coe_coe,AlgHom.toLinearMap_apply]; rw [ready_t,map_smul,TensorProduct.map_tmul,TensorProduct.lid_tmul]; rfl
lemma gen_value (J:Labels.Jet su)(x:PowerPair d)(t:ℝ): observation d J t (gen x)=(t:ℂ)^weight x • ready d J (gen x):=by
   unfold observation; rw [LinearMap.comp_apply,gen,ready_t,ready_t,scale_m]; change endor _ _ = _; rw [map_smul,pieces]; unfold UV.weight; simp_rw [pow_add,sky,smul_smul,Complex.ofReal_pow,pow_mul]; rw [mul_right_comm _ (Labels.read J _) _]
lemma one_scene (d:ℕ)(J:Labels.Jet su):observation d J 1=ready d J:=by apply (zBasis d).ext; intro i; rw [minted,gen_value]; simp
-- Measured order.
lemma painted (x:Pol d)(J:Labels.Jet su)(k:WithTop ℕ∞):ContDiff ℝ k (fun t=>observation d J t x):=by
   conv=> arg 3; ext t; rw [← (zBasis d).linearCombination_repr x]
   simp_rw [Finsupp.linearCombination_apply, Finsupp.sum,map_sum,map_smul,minted,gen_value]
   exact ContDiff.sum fun i _=>ContDiff.const_smul _ ((Complex.ofRealCLM.contDiff.pow _).smul contDiff_const)
lemma order_test (x:Pol d)(J:Labels.Jet su)(k:ℕ): iteratedDeriv k (fun t=> observation d J t x) 0=(k.factorial:ℂ) • ready d J (geometry k x):=by
   let B:= zBasis d; let s:= (B.repr x).support; let u:=B.repr x
   rw [← (show ∑ i∈s,u i • gen i=x from ?_)]
   · simp_rw [map_sum,map_smul]; rw [iteratedDeriv_fun_sum (fun i _=> ContDiffAt.const_smul _ ((painted (gen i) J _).contDiffAt))]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _
     rw [iteratedDeriv_fun_const_smul ((painted (gen i) J _).contDiffAt),geometry_basis]; simp_rw [gen_value,show ∀ t:ℝ,(t:ℂ)^weight i • ready d J (gen i)=(t^weight i:ℝ) • ready d J (gen i) from fun t=>by rw [← Complex.ofReal_pow]; rfl]; rw [iteratedDeriv_smul_const (contDiffAt_id.pow _), iteratedDeriv_fun_pow_zero]; by_cases hv:k=weight i
     · rw [if_pos hv,if_pos hv.symm, ← hv,smul_comm (↑(k.factorial):ℂ) _ _]; change u i • ((↑(k.factorial:ℝ):ℂ) • ready d J (gen i))=_; simp
     simp [hv, Ne.symm hv]
   simp_rw [← minted]; exact B.linearCombination_repr x
end Display
end YM.Massive.Poised
