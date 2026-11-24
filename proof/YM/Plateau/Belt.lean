import YM.Sprig.June
import YM.Oriole.Rhea
/-! Project simultaneously onto all the compatible scalar characters which isolate a block. Bound numerator at before L (auxiliary geometry in the fixed 8-dimensional-*level* UV only). -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
variable (hP:P.System)
variable (n: Side)(he:Injective (P.candidate d n 0))
open Massive.Oriole
section orth
open Submodule
variable {X:Type*} [AddCommGroup X][Module ℂ X][FiniteDimensional ℂ X]
variable (e:InnerProductSpace.Core ℂ X)
variable {I:Type*}(F:I→X≃ₗ[ℂ]X)(c:I→ℂ)(A:Submodule ℂ X)(hA:∀ x:X,x∈ A ↔∀ i,F i x=c i • x)
-- Given family invariant W for F,i all c etc, then orthogonal onto A maps W into W. and if quotient q(qp) is eigen, then projections. proof by projecting onto W to decompose.Orthogonal.
variable (G:Submodule ℂ X)(hf:∀ x: X,∀ i,x∈ G ↔ F i x ∈ G)(hχ:∀ x y i,e.inner (F i x) (F i y)=e.inner x y)
private lemma combo (G T:Submodule ℂ X)(h:Disjoint G T) (x y:X)(hx:x∈G)(hy:y∈ T)(hp:x+y=0):x=0∧y=0:=by
    have hx': x=-y:= eq_neg_of_add_eq_zero_left hp; have hP:= Submodule.disjoint_def.mp h x hx (hx'.symm ▸ T.neg_mem hy); rw[hP, zero_add] at hp; exact ⟨hP,hp⟩
include hf hχ
private lemma hereI (Y: Submodule ℂ X)(he:∀ x:X,x∈Y ↔∀ y∈G,e.inner y x=0) : (∀ i x,x∈Y→F i x∈Y):=by
       intro i x hx; apply (he _).mpr; intro y hy; obtain ⟨w,rfl⟩:= (F i).surjective y; rw [hχ]; exact (he x).mp hx w ((hf w i).mpr hy)
omit hf hχ
include hA
private lemma limbs {G B:Submodule ℂ X} (h:IsCompl G B)(hf:∀ x∈G,∀ i,F i x∈G)(he:∀ x∈B,∀ i,F i x∈B)(x y:X)(hp:x∈G)(hh:y∈B)(ht:x+y∈ A):x∈A ∧ y∈A:=by
       have hm(i): F i x-c i • x + (F i y-c i • y)=0:=by have hQ:= (hA _).mp ht i; rw [map_add,smul_add] at hQ; rw [←sub_eq_zero] at hQ; rw [← add_sub_add_comm]; exact hQ
       have hv(i):= combo G B h.disjoint _ _ (G.sub_mem (hf x hp i) (G.smul_mem _ hp)) (B.sub_mem (he y hh i) (B.smul_mem _ hh)) (hm i)
       exact ⟨(hA _).mpr fun i=>sub_eq_zero.mp (hv i).1, (hA _).mpr fun i=>sub_eq_zero.mp (hv i).2⟩
include hχ
lemma ports :∃ P:X→ₗ[ℂ] X,(∀ x,P x∈ A)∧(∀ x∈ A,P x=x)∧∀ (W:Submodule ℂ X), (∀ x i,x∈W ↔ F i x∈W)→ (∀ x∈W,P x∈W)∧(∀ x,(∀ i,F i x-c i • x∈W)→ x-P x ∈ W):=by
       letI : InnerProductSpace.Core ℂ X:=e
       letI : NormedAddCommGroup X:= e.toNormedAddCommGroup
       letI : PreInnerProductSpace.Core ℂ X := e.toCore
       letI : InnerProductSpace ℂ X:= .ofCore e.toCore
       letI : CompleteSpace A:= FiniteDimensional.complete ℂ _
       let P:= A.subtype ∘ₗ (A.orthogonalProjectionOnto).toLinearMap
       have hX(x): P x ∈ A:= (A.orthogonalProjectionOnto x).property
       have hp(x:X)(hx:x∈A):P x=x:=by change (A.orthogonalProjectionOnto (↑(⟨x,hx⟩:A))).val=_; rw [A.orthogonalProjectionOnto_mem_subspace_eq_self]
       refine ⟨P,hX,hp,fun W hf=>?_⟩; let Y:= Wᗮ; letI :CompleteSpace W:= FiniteDimensional.complete ℂ _; have hr: IsCompl W Y:=W.isCompl_orthogonal
       have hY:= hereI e F W hf hχ Y (fun x=>W.mem_orthogonal x)
       have hE(x:X)(hx:x∈W):P x∈W:=by
             let S:= P x; obtain ⟨p,h₁,q,h₂,h⟩:= Submodule.mem_sup.mp (show P x∈W⊔Y from hr.sup_eq_top.symm ▸ mem_top);
             have he:=limbs F c A hA hr (fun x h i=>(hf x i).1 h) (fun x h i=>hY i x h) p q h₁ h₂ (h.symm ▸ hX x)
             have hy:inner ℂ x q=0:=(W.mem_orthogonal _).mp h₂ x hx; have hz:inner ℂ p q=0:=(W.mem_orthogonal _).mp h₂ p h₁
             have hh:inner ℂ q (x-P x)=0 := (A.mem_orthogonal _).mp (A.sub_starProjection_mem_orthogonal x) q he.2 -- lemma stmt check
             have hu: q=0:=by
                   apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw[←h,inner_sub_right, ← inner_conj_symm q x,inner_add_right, ← inner_conj_symm q p] at hh; simpa [hy,hz] using hh -- syntax
             exact h ▸ (by rw [hu,add_zero]; exact h₁)
       refine ⟨hE,?_⟩; intro x hV
       obtain ⟨p,h₁,q,h₂,h⟩:= Submodule.mem_sup.mp (show x∈W⊔Y from hr.sup_eq_top.symm ▸ mem_top)
       have hh : q∈A:=by
             apply (hA q).mpr; intro i; apply sub_eq_zero.mp; apply Submodule.disjoint_def.mp hr.disjoint; swap; exact Y.sub_mem (hY i _ h₂) (Y.smul_mem _ h₂); specialize hV i; rw [←h,map_add,smul_add,add_sub_add_comm] at hV; exact (W.add_mem_iff_right (W.sub_mem ((hf _ _).mp h₁) (W.smul_mem _ h₁))).mp hV -- check order
       rw [←h,map_add,hp q hh,add_sub_add_right_eq_sub]; exact W.sub_mem h₁ (hE _ h₁)
end orth
end YM.Sprig
#print axioms YM.Sprig.ports
