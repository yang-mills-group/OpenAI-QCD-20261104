import YM.Next.MAXWELL.Beacon
import YM.Next.MAXWELL.Shelves
import YM.Heron.Palm
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct DawnS
open Maxwell.Free Maxwell
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Finset
variable {d:ℕ}
local notation "U"=> WickPol su
local notation "P"=> lowerCap su d
lemma wreath (s:Ortho)(p:GPol) : Maxwell.reduceEq (Labels.rotated s p)= reflectPol s (Maxwell.reduceEq p):=by
   apply equalPol; intro A; rw[reflects_eval,jet_value,jet_value,Labels.rotated,Labels.eval_changed]; apply congr_arg (fun X=>Labels.read X p); funext i; exact gauge_orient s⁻¹ _
lemma mintS (s:Ortho)(x:U)(hx:x∈P): reflectPol s x∈P:=by
    rw [← section_eq x, ← wreath]; exact reduces (Labels.moved_limit (lift_lim hx) _)
private theorem finiteS (d:ℕ):FiniteDimensional ℂ ↥(lowerCap su d):=by
    let F:↥(lowerCap su d)→ₗ[ℂ] ↥(Labels.limited su d):= { toFun:=fun x=>⟨_,lift_lim x.property⟩,map_add':=fun x y=> Subtype.ext (_root_.map_add _ x.val y.val),map_smul':=fun c x=>Subtype.ext (map_smul _ c x.val) }
    apply FiniteDimensional.of_injective F; intro a b h; apply Subtype.ext; exact (section_eq a.val).symm.trans ((congr_arg Maxwell.reduceEq (congr_arg Subtype.val h)).trans (section_eq b.val)) -- helper
variable (Δ:Ortho.Skew)(B: U)
lemma paintsL(W: Module.Dual ℂ U) : HasDerivAt (fun t=> W (reflectPol (Ortho.oneParameter Δ t) B)) (W (rewired (wheel su Δ) B)) 0:=by
    obtain ⟨d,h⟩:= cap_exists B; let K:= lowerCap su d; have hh:(rewired (wheel su Δ) B)∈ K:= rewire_bound _ _ h; let Q(t):↥K:= ⟨_,mintS (Ortho.oneParameter Δ t) B h⟩; let P':↥K:= ⟨_,hh⟩; let f(A:TaylorTower su): Module.Dual ℂ ↥K:= (probe A).toLinearMap.comp K.subtype
    letI:=finiteS d; have ht: Submodule.span ℂ (range f)=⊤:=by
         let D:=Submodule.span ℂ (range f); have hu:D.dualCoannihilator=⊥:=by
             apply le_antisymm _ bot_le; intro y hy; apply (Submodule.mem_bot ..).mpr; apply Subtype.ext; apply Maxwell.equalPol; intro x; rw [show probe x y.val=0 from (Submodule.mem_dualCoannihilator _).1 hy _ (Submodule.subset_span ⟨x,rfl⟩)]; exact (map_zero _).symm
         apply Submodule.eq_top_of_finrank_eq; have hm:=Subspace.finrank_add_finrank_dualCoannihilator_eq D; rw[hu,finrank_bot,add_zero] at hm; rw [hm, Subspace.dual_finrank_eq]
    have hp : ∀ W:Module.Dual ℂ ↥K, HasDerivAt (fun t=> W (Q t)) (W P') 0:=by
         intro W; let F: Submodule ℂ (Module.Dual ℂ ↥K) := { carrier:={W|HasDerivAt (fun t=>W (Q t)) (W P') 0}, add_mem':=@fun a b ha hb => HasDerivAt.add (show HasDerivAt (a ∘ Q) (a P') 0 from ha) hb, zero_mem':= hasDerivAt_const 0 (0:ℂ), smul_mem':=@fun c a ha => (show HasDerivAt (a ∘ Q) _ _ from ha).const_mul c }
         have hQ: ⊤ ≤ F:= by rw [← ht, Submodule.span_le]; rintro _ ⟨v,rfl⟩; exact writes_derivative v B Δ
         exact (show W∈ F from hQ Submodule.mem_top)
    exact hp (W.comp K.subtype)
end YM.Heron
#print axioms YM.Heron.paintsL
