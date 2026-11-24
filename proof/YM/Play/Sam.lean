import YM.Play.Lago
/-! # Quadrature sampler. Same branch tags.
 quantitative comparison on small event -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD Function MeasureTheory Filter Finset QCD.Grass QCD.Cove Matrix QCD.Beam QCD.Beam.Pipe Bera Anomaly
open scoped Topology ContDiff BigOperators Classical Matrix InnerProductSpace NNReal ENNReal
variable {A B:Type*}[MeasurableSpace A][MeasurableSpace B]{W: Type*}[NormedAddCommGroup W][NormedSpace ℝ W][CompleteSpace W]{κ:Measure A}{μ:Measure B} [IsProbabilityMeasure μ][IsProbabilityMeasure κ]{a d s c E:ℝ}
lemma petite {x:A×B→W}{y:B→W}(hx:Integrable x (κ.prod μ))(hy:Integrable y μ){K:Set B}(hp:MeasurableSet K)(hz:∀ z,z.2∈ Kᶜ→‖x z‖ ≤ s) (h:∀ z,z.2∈K→ ‖x z-y z.2‖ ≤ d) (hμ: μ.real Kᶜ ≤ E)(hY:(∫ z in Kᶜ,‖y z‖ ∂μ) ≤ a)(hd:0 ≤ d)(hs:0 ≤ s):
    ‖(∫ z,x z ∂κ.prod μ) - ∫ z,y z∂μ‖ ≤ d + (E*s + a) :=by
    let Z:Set (A×B):= Set.univ ×ˢ K; have hZ:MeasurableSet Z:= MeasurableSet.univ.prod hp
    let U :A×B → W:= y ∘ Prod.snd; let R:= κ.prod μ; have hU:Integrable U R:= hy.comp_snd κ
    have hi: (∫ z,y z ∂μ)=∫ z, U z ∂ R:=by unfold R; rw [integral_prod _ hU]; simp [U]
    rw [hi, ← integral_sub hx hU]
    let f z:= ‖x z-U z‖; have hf:Integrable f R:=(hx.sub hU).norm
    apply le_trans (norm_integral_le_integral_norm _)
    change (∫ z,f z ∂ R) ≤ _
    rw [← MeasureTheory.integral_add_compl hZ hf]; apply add_le_add
    · have hF:R.real Z ≤ 1:=by
           convert! measureReal_mono (μ:=κ.prod μ) (Set.subset_univ Z) (measure_ne_top _ _) using 1; simp
      exact (setIntegral_mono_on hf.restrict (integrable_const _) hZ (fun z hz=> h _ hz.2)).trans (le_trans (by rw [MeasureTheory.setIntegral_const, smul_eq_mul]) (mul_le_of_le_one_left hd hF)) -- cost syntax
    · have hr: Zᶜ= Set.univ ×ˢ Kᶜ:=by ext; simp [Z]
      let v z:=‖x z‖; let u z:=‖U z‖
      refine ((MeasureTheory.integral_mono hf.restrict ((hx.norm.add hU.norm).restrict) (show f ≤ v+u from fun i=> norm_sub_le _ _)).trans (?_))
      change (∫ z in Zᶜ, (‖x z‖ + ‖U z‖) ∂κ.prod μ) ≤ _; rw [integral_add hx.norm.restrict hU.norm.restrict]; apply add_le_add
      · have hf:(∫ z in Zᶜ,v z ∂ R) ≤ ∫ _ in Zᶜ,s ∂ R:= setIntegral_mono_on hx.norm.restrict (integrable_const _) hZ.compl (fun i hi=> hz _ (by rw [hr] at hi; exact hi.2)); refine hf.trans (?_); rw [MeasureTheory.setIntegral_const, hr]; unfold R Measure.real; rw [MeasureTheory.Measure.prod_prod]; simp only [measure_univ,one_mul,smul_eq_mul]; exact mul_le_mul_of_nonneg_right hμ hs
      · refine le_trans (b:=∫ z in Kᶜ,‖y z‖ ∂μ) (?_) hY; change (∫ z in Zᶜ,u z ∂κ.prod μ) ≤ _; rw [hr, ← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]; rw [MeasureTheory.integral_prod _ ?hp]; unfold u U; simp; exact hy.norm.restrict.comp_snd κ -- rewritten indices

lemma choo {T:Type*}[Fintype T][Nonempty T](f:T→W)(x:W)(h:∀ i,‖f i-x‖ ≤ s): ‖((Fintype.card T:ℝ)⁻¹ • ∑ i,f i)-x‖ ≤ s:=by
    let c:ℝ:= Fintype.card T; have hc:0<c:= Nat.cast_pos.mpr Fintype.card_pos; let g i:= f i-x; have hp:((Fintype.card T:ℝ)⁻¹ • ∑ i,f i)-x=c⁻¹ • ∑ i,g i:=by unfold g; rw [Finset.sum_sub_distrib,sum_const,← Nat.cast_smul_eq_nsmul ℝ,card_univ,smul_sub,smul_smul]; simp [c,hc.ne',(show (Fintype.card T:ℝ)≠0 from hc.ne')]
    rw [hp,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]; refine le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun i _=>h i)) (inv_nonneg.mpr hc.le)) (?_); simp only [sum_const,nsmul_eq_mul]; rw [card_univ]; unfold c at *; field_simp; try rfl
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.petite
