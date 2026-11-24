import YM.Mako.Tote
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Polynomial
open scoped Topology BigOperators Classical
open Vern
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W](S:Tide W)
variable (U V:Module.End ℂ W)
lemma semi(h:S.Leans U): Module.End.IsSemisimple U:=by
     let c:=S.coreP; letI :InnerProductSpace.Core ℂ W:=c
     letI:NormedAddCommGroup W:=c.toNormedAddCommGroup
     letI:PreInnerProductSpace.Core ℂ W:=c.toCore
     letI:InnerProductSpace ℂ W:=.ofCore c.toCore
     let J:= Complex.I • U; have hj:J.IsSymmetric:=by intro x y; change S.knot (Complex.I • U x) y=S.knot x (Complex.I • U y); rw[S.seals,S.sep,h]; simp
     exact (Module.End.IsSemisimple_smul_iff Complex.I_ne_zero).mp (Module.End.isFinitelySemisimple_iff_isSemisimple.mp hj.isFinitelySemisimple)
open Module
lemma bliss (T:Set W)(h:Submodule.span ℂ T=⊤):∃ B:Module.Basis (Fin (Module.finrank ℂ W)) ℂ W,∀ i,B i∈T:=by
      let p:= (show LinearIndepOn ℂ id (∅:Set W) from linearIndepOn_empty _ _); let B:= Basis.extendLe p (empty_subset T) h.ge -- names? want avoid I. use noncomputable
      letI := FiniteDimensional.fintypeBasisIndex B
      have he:= Module.finrank_eq_card_basis B; let f:= (Fintype.equivFinOfCardEq he.symm)
      refine ⟨B.reindex f,fun i=>?_⟩; rw [Basis.reindex_apply]; exact Basis.extendLe_subset _ _ _ (mem_range_self _)
lemma slice (h:Module.End.IsSemisimple U): Clear U:=by
     let T:Set W:={x|∃ a:ℂ,U x=a • x}; obtain ⟨B,hB⟩:= bliss T (by rw [eq_top_iff,← h.iSup_eigenspace_eq_top]; exact iSup_le (fun a x hx=> Submodule.subset_span (show x∈T from ⟨a,Module.End.mem_eigenspace_iff.mp hx⟩))) -- λ elaboration
     choose a ha using hB
     exact ⟨B,a,ha⟩
-- limit of orbit
variable {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y][FiniteDimensional ℂ Y]
variable (f:ℕ→ Y≃ₗ[ℂ]W)(P:Module.End ℂ W)(p:Module.End ℂ Y)
lemma spell_lim(h:∀ v:Y,Tendsto (fun i:ℕ=>(f i).symm (P (f i v))) atTop (𝓝 (p v)))(Q:Polynomial ℂ):∀ v:Y, Tendsto (fun i:ℕ=>(f i).symm (aeval P Q (f i v))) atTop (𝓝 (aeval p Q v)):=by
     let Tt(t:ℕ):Module.End ℂ Y:= (f t).symm.toLinearMap ∘ₗ P ∘ₗ (f t).toLinearMap
     have hg(n:ℕ)(v:Y): Tendsto (fun t:ℕ=>(f t).symm ((P^n) (f t v))) atTop (𝓝 ((p^n) v)):=by
             induction n with
             | zero=> simpa using tendsto_const_nhds (x:=v)
             | succ n ih=>
                rw [pow_succ' p]; apply (Iceberg.follows_L Tt p h _ _ ih).congr'
                apply Eventually.of_forall; intro i; simp [Tt,pow_succ']
     induction Q using Polynomial.induction_on' with
     | add p q h₁ h₂=> intro v; simp_rw [map_add,LinearMap.add_apply,map_add]; exact (h₁ v).add (h₂ v)
     | monomial n a=>
         intro v; rw[← C_mul_X_pow_eq_monomial]; simp only [map_mul,map_pow,aeval_C, aeval_X,Module.End.mul_apply,Module.algebraMap_end_apply,map_smul] -- algebra ℂ (End) noncomm evaluate
         exact tendsto_const_nhds.smul (hg n v)
lemma convoy_sem(h:∀ v:Y,Tendsto (fun i:ℕ=>(f i).symm (P (f i v))) atTop (𝓝 (p v)))(hp:P.IsSemisimple): p.IsSemisimple:=by
     apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.minpoly_squarefree; apply LinearMap.ext; intro v; have hv:= spell_lim f P p h (minpoly ℂ P) v; simp only [minpoly.aeval, LinearMap.zero_apply,map_zero] at hv; exact tendsto_nhds_unique hv tendsto_const_nhds
end YM.Mako
#print axioms YM.Mako.semi
#print axioms YM.Mako.slice
#print axioms YM.Mako.convoy_sem
