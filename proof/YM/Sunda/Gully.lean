import YM.Mako.Seed
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Set Function Analysis MeasureTheory QCD QCD.Lat Lattice
open Massive Work.A13
open scoped Topology Matrix Matrix.Norms.Frobenius InnerProductSpace BigOperators ComplexOrder
noncomputable def mainG := Subgroup.closure (Set.range Signed.inclusionO ∪ {x:Ortho|∃ i j:Axis,i≠j ∧ ∃ t:ℝ, Ortho.oneParameter (Ortho.plane i j) t=x})
lemma squash (i : Axis) (v : E4) (s : Finset Axis) (h : i ∉ s) :
    ∃ g ∈ mainG, ∀ j ∈ s, Ortho.move g v j = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, mainG.one_mem, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨hij, his⟩ := (show i ≠ j ∧ i ∉ s by simpa using h)
    obtain ⟨b, hb, hbs⟩ := ih his
    obtain ⟨t, ht⟩ := plane_eliminates hij (Ortho.move b v)
    let r := Ortho.oneParameter (Ortho.plane i j) t
    have hr : r ∈ mainG := Subgroup.subset_closure (Or.inr ⟨_, _,hij,t,rfl⟩)
    refine ⟨r * b, mainG.mul_mem hr hb, ?_⟩
    intro k hk
    rw [Ortho.move_mul]
    rcases Finset.mem_insert.mp hk with he | hm
    · subst k; exact ht
    have hki : k ≠ i := fun e => his (e ▸ hm)
    have hkj : k ≠ j := fun e => hj (e ▸ hm)
    exact ((plane_givens hij (Ortho.move b v) t).2.2 k hki hkj).trans (hbs k hm)

lemma align (i : Axis) (v : E4) :
    ∃ g ∈ mainG, ∃ c : ℝ, Ortho.move g v = c • basis i := by
  obtain ⟨g, hg, hall⟩ := squash i v (Finset.univ.erase i) (by simp)
  refine ⟨g, hg, Ortho.move g v i, PiLp.ext ?_⟩
  intro k
  by_cases h : k = i
  · subst k; simp
  simp [h, hall k (by simp [h])]

/-- All (genuine) hyperplane reflections come from conjugating just one mirror. -/
lemma reflection_conjugate (i : Axis) {v : E4} (hv : v ≠ 0) :
    ∃ g ∈ mainG,
      motionHom (g⁻¹ * Signed.reflect i * g) = (ℝ ∙ v)ᗮ.reflection := by
  obtain ⟨g, hg, c, hc⟩ := align i v
  refine ⟨g, hg, ?_⟩
  let f := motionHom g
  have he : f v = c • basis i := hc
  have hcn : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv (f.injective (by simpa using he))
  have ht : (ℝ ∙ v)ᗮ.map (f.toLinearEquiv : E4 →ₗ[ℝ] E4) = (ℝ ∙ basis i)ᗮ := by
    rw [Submodule.map_orthogonal_equiv, Submodule.map_span, Set.image_singleton]
    change (ℝ ∙ f v)ᗮ = _
    rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcn)]
  have hm : (ℝ ∙ basis i)ᗮ.reflection = f.symm.trans ((ℝ ∙ v)ᗮ.reflection.trans f) :=
    (congrArg (fun A : Submodule ℝ E4 => A.reflection) ht.symm).trans
      (Submodule.reflection_map f (ℝ ∙ v)ᗮ)
  rw [map_mul, map_mul, map_inv, motionHom_mirror]
  change f⁻¹ * (ℝ ∙ basis i)ᗮ.reflection * f = (ℝ ∙ v)ᗮ.reflection
  rw [hm]
  apply LinearIsometryEquiv.ext; intro x
  change f.symm (f ((ℝ ∙ v)ᗮ.reflection (f.symm (f x)))) = _
  simp

lemma reflection_mem (v : E4) :
    (ℝ ∙ v)ᗮ.reflection ∈ mainG.map motionHom := by
  by_cases hv : v = 0
  · subst v
    have he : (ℝ ∙ (0 : E4))ᗮ.reflection = 1 := by
      apply LinearIsometryEquiv.ext; intro x
      apply Submodule.reflection_mem_subspace_eq_self
      simp
    rw [he]; exact Subgroup.one_mem _
  obtain ⟨g, hg, he⟩ := reflection_conjugate timeAxis hv
  have hr : Signed.reflect timeAxis ∈ mainG :=
    Subgroup.subset_closure (Or.inl ⟨Signed.mirror timeAxis, rfl⟩)
  refine Subgroup.mem_map.mpr ⟨_, ?_, he⟩
  exact mainG.mul_mem (mainG.mul_mem (mainG.inv_mem hg) hr) hg

theorem answer : mainG =⊤ := by
  have h : ⊤ ≤ mainG.map motionHom := by
    rw [← LinearIsometryEquiv.reflections_generate]
    apply (Subgroup.closure_le _).mpr
    rintro r ⟨v, rfl⟩
    exact reflection_mem v
  apply (Subgroup.eq_top_iff' _).mpr
  intro g
  obtain ⟨b, hb, he⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_top (motionHom g)))
  rwa [← motionHom_injective he]

open Mako
lemma made (H:Subgroup EuPin)(h:∀ (p:EuPin) (s:Signed),p.Lifts s → p∈H)(hX:∀ i j:Axis,i≠j→∀ t:ℝ,oathU (Ortho.plane i j) t∈H)(x:EuPin): x∈H:=by
    have ht :⊤ ≤H.map euca:=by
         rw[← Sunda.answer]
         refine (Subgroup.closure_le _).mpr ?_
         rintro p (⟨s,rfl⟩|⟨i,j,hp,t,rfl⟩); · obtain ⟨q,hq⟩:= MassiveTwoEstimates.SpinGeometry.geometry.euclidean _; exact Subgroup.mem_map.mpr ⟨q,h _ s hq,hq⟩
         exact Subgroup.mem_map.mpr ⟨_,hX _ _ hp t,(tour _).2.2 t⟩
    obtain ⟨p,hp,he⟩:= Subgroup.mem_map.mp (ht (Subgroup.mem_top x.coord))
    have hx:EuPin.Lifts (x*p⁻¹) 1:=by change euca (x*p⁻¹) = Signed.inclusionO 1; rw [map_mul,map_inv,map_one,he]; exact mul_inv_cancel _
    have hy:=H.mul_mem (h _ _ hx) hp; rwa [mul_assoc,inv_mul_cancel,mul_one] at hy
end YM.Sunda
#print axioms YM.Sunda.made
