import YM.Massive.PCAC.Mark
/-! Constant and quadratic tests. Commute the derivatives before reading, keep output matrix flavor slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
lemma offGen (i j:A)(x:Alg A): coef ∅ (gen i j x)=0:=by
    have he(s:Finset A) : coef ∅ (atom j * mono s)=0:= spectrum (layer_mul (atom_mem _) (homogeneous _)) _ (by rw [Finset.card_empty]; omega)
    change coef ∅ (atom j * vary i x)=0; rw [← write (vary i x)]; simp_rw [mul_sum,mul_smul_comm,map_sum,map_smul,he,smul_zero, sum_const_zero]
lemma offMark (k : Bool)(T:Sour A)(x:Dirac A): coef ∅ (applyMark k T x)=0:=by cases k <;> simp [applyMark,offGen]
lemma first (i j k:A)(x:Alg A): vary i (gen j k x)= gen j k (vary i x) + if i=k then vary j x else 0:=by
    change vary i (atom k*vary j x) = (atom k* vary j (vary i x)) + _; rw [vary_head,show vary i (vary j x)= _ from (CliffordAlgebra.contractLeft_comm _ _ x : vary i (vary j x)= -(vary j (vary i x)))]; split_ifs with h
    · subst k; simp [probe,add_comm]; rfl
    simp [probe,h]; rfl
lemma useB (i:A)(M:Sour A)(x:Dirac A): vary (.inl i) (applyMark false M x) = applyMark false M (vary (.inl i) x)+ ∑ k:A,M k i • vary (.inl k) x:=by simp_rw [column,map_sum,map_smul, first,smul_add,sum_add_distrib]; simp
lemma useW (i:A)(M:Sour A)(x:Dirac A): vary (.inr i) (applyMark true M x) = applyMark true M (vary (.inr i) x)+ ∑ k:A,M i k • vary (.inr k) x:=by simp_rw [row,map_sum,map_smul, first,smul_add,sum_add_distrib]; simp
lemma useWB (i:A)(M:Sour A)(x:Dirac A): vary (.inr i) (applyMark false M x)=applyMark false M (vary (.inr i) x):=by simp_rw [column,map_sum,map_smul,first]; simp
lemma useBW (i:A)(M:Sour A)(x:Dirac A): vary (.inl i) (applyMark true M x)=applyMark true M (vary (.inl i) x):=by simp_rw [row,map_sum,map_smul,first]; simp
-- negate derivative. This is the coefficient cov detector ψ,bar.
abbrev traceP (X:Dirac A): Sour A := Matrix.of fun i j=> -(coef ∅ (pairD j i X))
lemma quote (b:Bool)(V:Sour A)(X:Dirac A): traceP (applyMark b V X)= if b then V*traceP X else traceP X*V:=by
    ext i j; cases b
    · change -(coef ∅ (vary (.inl j) (vary (.inr i) (applyMark false V X))))= (traceP X* V) i j
      rw [useWB,useB,map_add,offMark,zero_add,map_sum,Matrix.mul_apply]; simp_rw [map_smul,smul_eq_mul]; rw [← sum_neg_distrib]; exact sum_congr rfl fun i _=> by change _= -(_)*_; simp only [pairD,LinearMap.comp_apply];ring -- ring defeq pairD?
    change -(coef ∅ (vary (.inl j) (vary (.inr i) (applyMark true V X))))= (V*traceP X) i j; rw [useW,map_add,useBW,map_add,offMark,zero_add,map_sum,map_sum,Matrix.mul_apply]; simp_rw [map_smul,smul_eq_mul]; rw [← sum_neg_distrib]; exact sum_congr rfl fun l _=> by change _= V i l* - _; simp only [pairD,LinearMap.comp_apply];ring
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.quote
