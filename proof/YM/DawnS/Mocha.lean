import YM.DawnS.Figs
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
variable {d:ℕ}
lemma slashTint (d:ℕ) : slashEq d ≤ (slashEq d).comap (adjLine d):=by
    apply Submodule.span_le.mpr; rintro i (⟨⟨⟨p,a,b⟩,c⟩,rfl⟩|⟨⟨⟨p,a,b⟩,c⟩,rfl⟩)
    · apply Submodule.mem_comap.mpr; rw[climbs]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨_,rfl⟩))
    apply Submodule.mem_comap.mpr; rw[cinders]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨_,rfl⟩))
local notation "PV"=> bareT d
local notation "τL"=> adjLine d
lemma folds(v w:beam d)(he: (slashEq d).mkQ v=(slashEq d).mkQ w): (slashEq d).mkQ (τL v)=(slashEq d).mkQ (τL w):=by apply sub_eq_zero.mp; rw [← map_sub, ← map_sub]; exact (Submodule.Quotient.mk_eq_zero _).mpr (show _ from slashTint d ((Submodule.Quotient.mk_eq_zero _).1 (show (slashEq d).mkQ (v-w)= 0 from (by rw [map_sub,he,sub_self]))))
lemma τSpin_one(d:ℕ): τSpin d 1=1:=by unfold τSpin; rw[LinearMap.comp_apply,Grass.dagger_one, AlgHom.toLinearMap_apply,map_one]
lemma τSpin_mul(x y: SpinPol d): τSpin d (x*y)=τSpin d y*τSpin d x:=by unfold τSpin;simp only [LinearMap.comp_apply,Grass.dagger_mul, AlgHom.toLinearMap_apply,map_mul]
lemma τSpin_ltr(x:SpinPol d)(Z:scarG d→ₗ[ℂ] beam d)(hz:(slashEq d).mkQ.comp Z=LinearMap.id): bareT d (τSpin d x) = bareT d (τSpin d (ExteriorAlgebra.map Z (bareT d x))):=by
     induction x using ExteriorAlgebra.induction with
     | algebraMap z => simp only [AlgHom.commutes,Algebra.algebraMap_eq_smul_one,τSpin_one,map_smul,map_smulₛₗ,map_one]
     | add x y hx hy => rw [map_add,map_add,hx,hy,map_add,map_add,map_add,map_add]
     | mul x y hx hy => rw [τSpin_mul,map_mul,hx,hy,map_mul,map_mul,τSpin_mul,map_mul]
     | ι v=> rw[show ExteriorAlgebra.map Z (bareT d (line v)) = line (Z ((slashEq d).mkQ v)) from ?_,legged,legged]; swap; · rw[bareT]; simp only[line,ExteriorAlgebra.map_apply_ι] -- simp
             unfold bareT; rw [ExteriorAlgebra.map_apply_ι,ExteriorAlgebra.map_apply_ι]; exact congr_arg _ (folds v _ (LinearMap.congr_fun hz _|>.symm))
lemma confined(x y:SpinPol d)(he: bareT d x= bareT d y):bareT d (τSpin d x)=bareT d (τSpin d y):=by
     obtain ⟨Z,h⟩:=(slashEq d).mkQ.exists_rightInverse_of_surjective (slashEq d).range_mkQ; exact Eq.trans (τSpin_ltr x Z h) (by rw[he,←τSpin_ltr y Z h])
end YM.DawnS
#print axioms YM.DawnS.confined
