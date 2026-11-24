import YM.Talis.Quills
import YM.Avena.Films
/-!
  Choose regulator stencils from precise grade. Book at fixed input horizon. Structured before-L menus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
open Poised Poised.Plans Poised.Stative Poised.Sieve Display
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
namespace Vale
variable {d D:ℕ}
lemma slim (p: UV.GPol)(i:Powers) : life i≤ Labels.height i:=by unfold life Labels.height; rw [Finsupp.weight_apply]; apply Finset.sum_le_sum; intro j _; change i j ≤ i j* (j.1+2); nlinarith
lemma wane (j:Jars d): j.val.2.1 ≤ j.val.1 ∧ j.val.2.2 ≤ j.val.1 :=by
    obtain ⟨i,hi,hp⟩:=Finset.mem_image.mp j.property
    rw [←hp]; constructor
    · exact (slim 0 i.1).trans (show Labels.height i.1 ≤ _ from (le_trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 <2)) (le_add_of_nonneg_right (Nat.zero_le _)))) -- notation
    have hv :∀ p:Pairs (SpinMode d), 1 ≤ letterWeight p:=fun p=> by unfold letterWeight spinWeight;omega
    have h : i.2.card ≤ ∑ j∈i.2,letterWeight j:=by simpa using (Finset.sum_le_sum (s:=i.2) (fun i _=>hv i))
    exact h.trans (le_add_of_nonneg_left (Nat.zero_le _)) -- syntax fix
abbrev Stokes (d:ℕ) := Fin (Module.finrank ℂ (Symbol d))
structure Text (d:ℕ) where
    mark : Label d
    era : Jars d
    stamp : mark.val ∈ Rtg d era.val.1 era.val.2.1 era.val.2.2
lemma draws {V:Type}[AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V] (s:Set V) (hs:Submodule.span ℂ s= ⊤) : ∃ f: Fin (Module.finrank ℂ V) → V,(∀ i,f i∈s) ∧ Submodule.span ℂ (Set.range f)= ⊤ ∧ LinearIndependent ℂ f :=by
     have he:= Submodule.exists_fun_fin_finrank_span_eq ℂ s; rwa [hs,finrank_top] at he
lemma planets (d:ℕ) : ∃ F:Stokes d→ Text d, ∃ B: Module.Basis (Stokes d) ℂ (Symbol d),∀ i,B i=projection (F i).mark:=by
    let f(i:Text d) : Symbol d:= projection i.mark; let S:=Set.range f
    have ht : Submodule.span ℂ S=⊤:=by
       refine eq_top_iff.mpr fun w _=>?_ ; obtain ⟨t,rfl⟩:= (onto (d:=d) w); rw [←sumCut t,map_sum]; refine Submodule.sum_mem _ fun i _=>Submodule.subset_span ?_; exact ⟨⟨_,i, Massive.Evo.canCut i.val t.val⟩,rfl⟩
    have he:=draws (V:=Symbol d) S ht
    obtain ⟨A,hA,hP,hM⟩:=he; choose F hf using hA; let Q:= Module.Basis.mk hM hP.ge; exact ⟨F,Q,fun i=> (Module.Basis.mk_apply hM hP.ge i).trans (hf i).symm⟩
noncomputable def GlyphV (F:Text d)(D:ℕ)(h:d≤D): Glyph D:=let i:=F.era.val; ⟨d,i.1,i.2.1,i.2.2,F.mark,h,jar_w _,((wane F.era).1.trans (jar_w _)).trans h,((wane F.era).2.trans (jar_w _)).trans h,F.stamp,Classical.choose (Massive.Evo.boarded _ F.stamp),Classical.choose_spec (Massive.Evo.boarded _ F.stamp)⟩
variable (sym:UV.RawSym)
noncomputable def opposite (p:Axis)(x:Text d): Text d where
    mark:= sym.adj d p x.mark
    era:= x.era
    stamp := Massive.Evo.reflected p sym x.mark x.stamp
structure Laurel(d:ℕ) where
    F : Stokes d→ Text d
    B : Module.Basis (Stokes d) ℂ (Symbol d)
    h :∀ i,B i=projection (F i).mark
lemma born (d:ℕ):Nonempty (Laurel d):=by obtain ⟨F,B,H⟩:=planets d; exact ⟨F,B,H⟩
lemma living (H:Laurel d) (i:Stokes d): (H.F i).mark≠0 := fun h=> H.B.ne_zero i (by rw[H.h,h,map_zero])
end Vale
end YM.Intag
#print axioms YM.Intag.Vale.born
#print axioms YM.Intag.Vale.GlyphV
