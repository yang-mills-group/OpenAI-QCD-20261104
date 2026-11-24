import YM.DawnS.Tastes
import YM.Elms.Ideal

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Pointwise
open Arise.Pair Arise.Count
variable {d n m k :ℕ}{u:Fin n→ℕ}
lemma planted(g:Maxwell.WickPol su): Maxwell.reduceEq (Elm.draw su g)=g:=by
    apply Maxwell.equalPol; intro p
    rw[Maxwell.jet_value, Elm.draw_value]; congr 2; funext i; apply LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr Maxwell.leg_injective)
variable (x:Points n)(hx:x∈conf n)
local notation "QZ"=>chime u x
local notation "G"=> unionB (chime u x)
variable (i:Fin n)
include hx
lemma stroll(g:Fin n→ UV.GPol)(f:(i:Fin n)→ SpinPol (u i)) : UV.Free.moment u x (fun i=>g i ⊗ₜ[ℂ] f i)= Maxwell.Wick.moment su x (fun i=> Maxwell.reduceEq (g i))*lease QZ (List.ofFn (fun i=> twig u i (f i))).prod:=by
    let K:= Occ u; let y(i:Fin n):=x i; have h:= Arise.Count.gammaCost (U:=Unit) (Fin n) id u y hx g f -- includes id
    change Maxwell.Wick.moment su x (fun i=> Maxwell.reduceEq (g i)) • (erg (Fin n) y u (List.ofFn fun i:Fin n=>ham (Fin n) i u (f i)).prod)=UV.Free.moment u x (fun i=>g i⊗ₜ[ℂ] f i) • (1:Alg Unit) at h
    have H:=congr_arg (Grass.coef (∅:Finset Unit)) h
    rw [map_smul,map_smul,show Grass.coef ∅ (1:Alg Unit)=1 from ?_] at H; simp_rw[edge,smul_eq_mul,mul_one] at H; exact H.symm
    rw [←mono_empty (A:=Unit),Grass.read]
-- Passport via tensor comps
lemma balanced(ξ:∀ i:Fin n,scarG (u i)→ₗ[ℂ]beam (u i))(hξ:∀ i:Fin n,(slashEq (u i)).mkQ.comp (ξ i)=LinearMap.id) (f:(i:Fin n)→SpinPol (u i)) : lease QZ (List.ofFn (fun i=> twig u i (f i))).prod=lease QZ (List.ofFn (fun i=>twig u i (ExteriorAlgebra.map (ξ i) (bareT (u i) (f i))))).prod:=by
     let p(i:Fin n):=twig u i (f i); let q(i:Fin n):= twig u i (ExteriorAlgebra.map (ξ i) (bareT (u i) (f i)))
     have h(l:List (Fin n))(a:Alg (Occ u)): lease QZ (a*(l.map p).prod)=lease QZ (a*(l.map q).prod):=by
         induction l generalizing a with|nil=>rfl|cons i l ih=> rw [List.map_cons,List.prod_cons,←mul_assoc, List.map_cons,List.prod_cons,←mul_assoc]; exact (ih _).trans (waist x hx i (ξ i) (hξ i) (f i) a _)
     have h':=h (List.finRange n) 1; rw [one_mul,one_mul,List.finRange,List.map_ofFn,List.map_ofFn] at h'; exact h'
noncomputable abbrev fish(i:Fin n)(ξ:∀ i:Fin n,scarG (u i)→ₗ[ℂ]beam (u i)) : Maxwell.WickPol su ⊗[ℂ] wedgeR (u i) →ₗ[ℂ] Pol (u i):=TensorProduct.map (Elm.draw su).toLinearMap (ExteriorAlgebra.map (ξ i)).toLinearMap
lemma lowly (ξ:∀ i:Fin n,scarG (u i)→ₗ[ℂ]beam (u i))(hξ:∀ i:Fin n,(slashEq (u i)).mkQ.comp (ξ i)=LinearMap.id) :UV.Free.moment u x=(UV.Free.moment u x).compLinearMap (fun i=>(fish i ξ).comp (UV.Free.reduceEq)):=by
     apply roof _ _ (fun i=> UV.Free.basisU _); intro v; let P(i:Fin n):= ((MvPolynomial.basisMonomials _ ℂ) (v i).1); let Y(i:Fin n):=(Grass.blades _) (v i).2
     have hT (i:Fin n) : basisU _ (v i)=P i⊗ₜ[ℂ] (Y i):= Module.Basis.tensorProduct_apply ..
     simp_rw[hT]; rw[stroll x hx P Y,MultilinearMap.compLinearMap_apply]; simp only [LinearMap.comp_apply,fish,UV.Free.reduceEq,TensorProduct.map_tmul,AlgHom.toLinearMap_apply]; rw [stroll]; simp_rw [planted]; exact congr_arg _ (balanced x hx ξ hξ Y); exact hx
lemma descendant (A B:(i:Fin n)→ Pol (u i))(h:∀ i:Fin n, UV.Free.reduceEq (A i)=UV.Free.reduceEq (B i)): UV.Free.moment u x A = UV.Free.moment u x B:=by
     choose ξ hξ using fun i:Fin n=>(slashEq (u i)).mkQ.exists_rightInverse_of_surjective (slashEq (u i)).range_mkQ
     rw[lowly x hx ξ hξ]; simp_rw[MultilinearMap.compLinearMap_apply,LinearMap.comp_apply,h]
lemma trails (A B : (i:Fin n)→ Label (u i))(h:∀ i,projection (A i)=projection (B i)) : wick u x A=wick u x B:=descendant x hx (fun i=>(A i).val) (fun i=>(B i).val) fun i=> congr_arg Subtype.val (h i)
end YM.DawnS
#print axioms YM.DawnS.trails
