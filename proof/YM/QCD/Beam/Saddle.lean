import YM.QCD.Beam.Number
/-! # tensorize independence criterion. full normed coefficient space -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam
open Filter Lattice Set MeasureTheory Finset Function RG
open scoped Topology BigOperators ContDiff Classical
variable {ι ρ A M N:Type*}[NormedCommRing M][NormedAlgebra ℝ M]
variable [Fintype ι] [MeasurableSpace ρ] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [FiniteDimensional ℝ M]
-- use fintype entirely to avoid masked. ∫prod-of-scalars criterion
lemma prodSaddle (f : ι→ℝ)(g:ι→M): ∏ i:ι, f i • g i= (∏ i, f i) •∏ i, g i:=by
   let s (p:Finset ι):=p; suffices H : ∀ p:Finset ι, ∏ i∈p,f i • g i=(∏ i∈p,f i) • ∏ i∈p,g i by exact H _
   intro p; induction p using Finset.induction_on with
   | empty=> simp
   | insert i p hi ih=> simp only [prod_insert hi,ih,smul_mul_smul_comm]
lemma distributeF [Fintype A](v:ι→A→M):∏ i:ι, ∑ a:A,v i a=∑ w:ι→A,∏ i:ι, v i (w i) :=by classical exact Fintype.prod_sum _ -- inspect
lemma envScalar (L:A→ℝ) (h:∀ i:A,0≤L i):∀ p:Finset A,0≤∏ i∈p,L i:=fun _=>prod_nonneg fun _ _=>h _
lemma envCasting (s:Finset A)(f:A→ρ→M)(h:∀ i∈s,Envelope (f i)) : Envelope fun x=>∏ i∈s, f i x :=by
   induction s using Finset.induction_on with
   | empty=> simp; exact ⟨measurable_const,‖(1:M)‖,fun _=> le_rfl⟩
   | insert i s hi ih=>
     simp only [prod_insert hi]; have hx:=h i (mem_insert_self ..)
     obtain ⟨C,hC⟩ := hx.cost; let p (x:ρ):=∏ i∈s,f i x
     have ht:Envelope p:= ih (fun i hh=> h i (mem_insert_of_mem hh))
     obtain ⟨D,hD⟩ := ht.cost
     exact ⟨hx.meas.mul ht.meas, C*D,fun x=>by exact (norm_mul_le _ _).trans (mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))⟩
lemma envCLM [NormedAddCommGroup N][MeasurableSpace N][BorelSpace N][NormedSpace ℝ N] (v:M→L[ℝ]N)(p:ρ→M)(h:Envelope p): Envelope (v ∘ p):= by
   obtain ⟨C,H⟩:= h.cost; exact ⟨v.measurable.comp h.meas,‖v‖*C, fun i=> (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left (H i) (norm_nonneg _))⟩
variable [CompleteSpace M]

lemma wideProd (f: ι→ρ→M) (μ:Measure ρ)[IsFiniteMeasure μ](hf:∀ i,Envelope (f i))(h : ∀ (g:ι→M→L[ℝ]ℝ),(∫ t, ∏ i,g i (f i t) ∂μ)=∏ i,∫ t,g i (f i t) ∂μ):
   (∫ t,∏ i,f i t ∂μ)= ∏ i,∫ t,f i t ∂μ:=by
    let B:=Module.finBasis ℝ M
    let A:= Fin (Module.finrank ℝ M)
    let v (i:A): M→L[ℝ]ℝ:=LinearMap.toContinuousLinearMap (B.coord i)
    have hv (m:M): ∑ i:A, v i m • B i=m:= B.sum_repr m
    have hx (t:ρ):∏ i,f i t=∑ p:ι→A,(∏ i,v (p i) (f i t)) • ∏ i,B (p i):=by
       rw [show (∏ i,f i t)=∏ i,∑ j:A,v j (f i t) • B j from prod_congr rfl fun i _=>(hv _).symm, distributeF]; exact sum_congr rfl fun i _=> prodSaddle ..
    have he i: v i= v i:=rfl
    have hp(p:ι→A): Integrable (fun t=> ∏ i, v (p i) (f i t)) μ:= Envelope.integrable (envCasting univ (fun i=> (v (p i)) ∘ (f i)) (fun i _=>envCLM (v _) (f i) (hf i))) _
    simp_rw [hx]; rw [integral_finsetSum _ (fun i _=> (hp i).smul_const _)]
    have hG (p:ι→A): (∫ t, ∏ i,v (p i) (f i t) ∂μ)=∏ i,∫ t,v (p i) (f i t) ∂μ:= h (fun i=>v (p i))
    simp_rw [integral_smul_const,hG,ContinuousLinearMap.integral_comp_comm (v _) (envPlot (hf _) _)] -- _ placeholders
    rw [show (∏ i,∫ t,f i t ∂μ)= ∏ i,∑ a:A,v a (∫ t,f i t ∂μ) • B a from prod_congr rfl fun i _=> (hv _).symm,distributeF]; exact Eq.symm <| sum_congr rfl fun i _=> prodSaddle ..
-- finite unmeasured analog use pure arithmetic and basis decomposition
abbrev choiceS [Fintype A](f:A→M):=(Fintype.card A:ℝ)⁻¹ • ∑ i,f i
lemma volProd [Fintype A](f:ι→A→M)(h:∀ (g:ι→M→L[ℝ]ℝ),choiceS (fun i=> ∏ j, g j (f j i))= ∏ j,choiceS (g j ∘ f j)):
   choiceS (fun i=> ∏ j,f j i)=∏ j,choiceS (f j):=by
    let B:=Module.finBasis ℝ M
    let P:= Fin (Module.finrank ℝ M)
    let v (i:P): M→L[ℝ]ℝ:=LinearMap.toContinuousLinearMap (B.coord i)
    have hv (m:M): ∑ i:P, v i m • B i=m:= B.sum_repr m
    have hx(i:A):∏ j,f j i=∑ p:ι→P,(∏ j,v (p j) (f j i)) • ∏ j,B (p j):=by rw [show (∏ j,f j i)=∏ j,∑ a:P,v a (f j i) • B a from prod_congr rfl fun i _=>(hv _).symm,distributeF]; exact sum_congr rfl fun i _=> prodSaddle ..
    have hp (p:ι→P):(Fintype.card A:ℝ)⁻¹ • (∑ i:A, (∏ j,v (p j) (f j i)) •∏ j,B (p j))=(∏ j, v (p j) (choiceS (f j))) • ∏ j,B (p j) :=by
       rw [← sum_smul,← mul_smul] -- edit
       refine congr_arg (fun s:ℝ=> s •(∏ j,B (p j))) ((h (fun i=> v (p i))).trans (prod_congr rfl (fun i _=>?_)))
       unfold choiceS; simp
    change (Fintype.card A:ℝ)⁻¹ • ∑ i:A,(∏ j, f j i)=∏ j,choiceS (f j)
    simp_rw [hx]; rw [Finset.sum_comm,Finset.smul_sum]; simp_rw [hp]
    change _=∏ j,choiceS (f j)
    rw [show (∏ i,choiceS (f i))= ∏ i,∑ a:P,v a (choiceS (f i)) • B a from prod_congr rfl fun i _=> (hv _).symm,distributeF]; exact Eq.symm <| sum_congr rfl fun i _=> prodSaddle ..
end YM.QCD.Beam
