import YM.DawnS.Ritual

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Pointwise
open Arise Creek Arise.Count -- Count.callS
variable {d n m k:ℕ}(u: Fin n→ℕ)
abbrev letters(d:ℕ):= Pairs (SpinMode d)
abbrev beam(d:ℕ):= Seed (letters d)
noncomputable def rifle (i:Fin n): beam (u i) →ₗ[ℂ] Seed (Occ u):= (thetaBasis (letters (u i))).constr ℂ fun k=>thetaBasis _ (⟨i,k⟩:Occ u)
lemma mounted (i:Fin n)(k:letters (u i)): rifle u i (thetaBasis _ k)=thetaBasis _ (⟨i,k⟩:Occ u):=Module.Basis.constr_basis ..
noncomputable abbrev twig (i:Fin n):SpinPol (u i)→ₐ[ℂ] Alg (Occ u):=ExteriorAlgebra.map (rifle u i)
lemma edge (i:Fin n) : ham _ i u=twig u i:=by
    apply ExteriorAlgebra.hom_ext; apply (thetaBasis _).ext; intro k
    change ham _ i u (atom k)=twig _ _ (line (thetaBasis _ k)); rw [show twig u i (line _)=_ from ExteriorAlgebra.map_apply_ι _ _, mounted]; exact embed_atom ..
-- core single pair on line
variable {u}
variable (x:Points n) (hx:x∈conf n)
noncomputable def chime (u:Fin n→ℕ)(x:Points n): Matrix (Occ u) (Occ u) ℂ:= callS (fun i=>x i) u
local notation "QZ"=>chime u x
include hx
lemma sector(i j:Occ u): unionB QZ (thetaBasis _ i) (thetaBasis _ j)=UV.Free.pair x i j:=by rw[skyZ]; exact (nextX x hx u i j).symm
lemma quiets(i:Fin n)(z w:beam (u i)): unionB QZ (rifle u i z) (rifle u i w)=0:=by
     rw[←(thetaBasis _).sum_repr z,← (thetaBasis _).sum_repr w]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]; refine sum_eq_zero fun j _=> ?_; -- sum order
     simp_rw [mounted,sector x hx]; simp [UV.Free.pair]
lemma col_gone (i:Fin n)(j:SpinMode (u i))(k:Occ u): unionB QZ (rifle u i (slashCol j)) (thetaBasis _ k)=0:=by
     unfold slashCol; simp only [map_sum,LinearMap.sum_apply]; obtain ⟨t,w|w⟩:=k
     · refine sum_eq_zero fun a _=>sum_eq_zero fun b _=>sum_eq_zero fun p _=>?_ ; split_ifs; next h=> rw [map_smul,map_smul, LinearMap.smul_apply,mounted,sector x hx]; simp [UV.Free.pair]
       rw[map_zero,map_zero,LinearMap.zero_apply]
     by_cases h:i=t;
     · subst t; refine sum_eq_zero fun a _=>sum_eq_zero fun b _=>sum_eq_zero fun p _=>?_ ; split_ifs; next h=> rw[map_smul,map_smul,LinearMap.smul_apply,mounted,sector x hx]; simp [UV.Free.pair]
       rw[map_zero,map_zero,LinearMap.zero_apply]
     refine Eq.trans ?_ (slashL (x i) (x t) ((show Injective x.ofLp from hx).ne h) j w); refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>sum_congr rfl fun k _=>?_ ; split_ifs; next hh=> rw[map_smul,map_smul,LinearMap.smul_apply,mounted,sector x hx]; simp [UV.Free.pair,h]
     rw[map_zero,map_zero,LinearMap.zero_apply]
lemma bar_gone (i:Fin n)(j:SpinMode (u i))(k:Occ u): unionB QZ (rifle u i (slashBar j)) (thetaBasis _ k)=0:=by
     unfold slashBar; simp only [map_sum,LinearMap.sum_apply]; obtain ⟨t,w|w⟩:=k; swap
     · refine sum_eq_zero fun a _=>sum_eq_zero fun b _=>sum_eq_zero fun p _=>?_ ; split_ifs; next h=> rw [map_smul,map_smul, LinearMap.smul_apply,mounted,sector x hx]; simp [UV.Free.pair]
       rw[map_zero,map_zero,LinearMap.zero_apply]
     by_cases h:i=t;
     · subst t; refine sum_eq_zero fun a _=>sum_eq_zero fun b _=>sum_eq_zero fun p _=>?_ ; split_ifs; next h=> rw[map_smul,map_smul,LinearMap.smul_apply,mounted,sector x hx]; simp [UV.Free.pair]
       rw[map_zero,map_zero,LinearMap.zero_apply]
     apply neg_injective; rw [neg_zero, ←sum_neg_distrib] -- sign? lemma wrong forward
     simp_rw[←sum_neg_distrib]
     refine Eq.trans ?_ (slashR (x t) (x i) ((show Injective x.ofLp from hx).ne (Ne.symm h)) j w); refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>sum_congr rfl fun k _=>?_ ; split_ifs; next hh=> rw[map_smul,map_smul,LinearMap.smul_apply,mounted,sector x hx]; simp [UV.Free.pair,h]
     simp
end YM.DawnS
