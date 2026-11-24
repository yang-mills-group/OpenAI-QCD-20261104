import YM.Bank.Pap
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Pap
open Function Lattice Laurent Bloch Metric Precision MeasureTheory Filter
open Finset Pilot
open QCD.Pearl (beamP beam0 beamH ix)
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
lemma null_plane (i:Axis)(a:ℝ): volume {x:E4| x i=a}= 0 :=by
   let f(j:Axis):Set ℝ:=if i=j then {a} else Set.univ
   let S:= Set.univ.pi f; have hh : {x:E4|x i=a}=ix ⁻¹' S:=by ext x; simp only [Set.mem_setOf_eq,Set.mem_preimage,S,Set.mem_univ_pi]; constructor; intro h j; by_cases he:i=j; simp [f, ← he,h,← show x.ofLp=ix x from rfl]; simp [f,he]; exact fun h=> Set.mem_singleton_iff.mp (by simpa only [f,if_true] using (h i) : ix x i∈ ({a}:Set ℝ))
   have hT : Measure.map ix volume= volume:= (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis).map_eq
   rw [hh,← Measure.map_apply ix.measurable, hT]; change Measure.pi (fun _ : Axis=>volume) _=0; rw [Measure.pi_pi]; exact prod_eq_zero (mem_univ i) (by simp[f]); exact MeasurableSet.univ_pi fun i=> by unfold f; split<;>simp
lemma hollow : IsOpen coast:=by classical unfold coast; rw [Set.setOf_forall]; exact isOpen_iInter_of_finite fun i=> isOpen_lt (show Continuous (fun x:E4=> |x i|) by fun_prop) continuous_const
lemma within (σ:Bool){x:E4}(f:E4→V)(h:x∈coast)(hc:ContinuousAt f x):Tendsto (fun c:Side=> wing c σ f x) atTop (𝓝 (f x)):=by
    rw [Metric.tendsto_nhds]; intro ε he
    obtain ⟨δ,hδ,hD⟩:=Metric.continuousAt_iff.mp hc ε he
    filter_upwards [inland_f σ h,beam0.eventually (gt_mem_nhds hδ)] with c hc hb
    obtain ⟨p,hp⟩:=hc; rw [wing_place f hp]; exact hD ((dist_comm ..).trans_le (place_far hp)|>.trans_lt hb)
open scoped Classical in
lemma oversees (σ:Bool) (f:E4→V)(h:∀ x∈coast,x≠0→ContinuousAt f x):∀ᵐ x:E4, Tendsto (fun c:Side=>wing c σ f x) atTop (𝓝 (coast.indicator f x)):=by
    have he (i:Axis) a: ∀ᵐ (x:E4),x i≠ a:= by apply ae_iff.mpr; simpa only [not_not] using! null_plane i a
    filter_upwards [ae_all_iff.mpr (fun i=> he i Real.pi),ae_all_iff.mpr (fun i=> he i (-Real.pi)),(show ∀ᵐ x:E4,x ≠ 0 from (compl_mem_ae_iff.mpr (measure_singleton _)))] with x hd hD hx
    by_cases hp:x∈coast; rw [Set.indicator_of_mem hp]; exact within _ _ hp (h x hp hx)
    rw [Set.indicator_of_notMem hp]; apply tendsto_const_nhds.congr'
    unfold coast at hp; simp only [Set.mem_setOf_eq] at hp; obtain ⟨i,hi⟩:= not_forall.mp hp
    have hk: Real.pi< |x i|:= lt_of_le_of_ne (le_of_not_gt hi) (fun h=> by
      rcases le_total (x i) 0 with ha|ha
      · rw [abs_of_nonpos ha] at h; exact hD i (by linarith)
      rw [abs_of_nonneg ha] at h; exact hd i h.symm)
    filter_upwards [sailing σ (x:=x) ⟨i,hk⟩] with c hc; exact (wing_no f hc).symm
lemma follows (σ:Bool){K:ℝ}(hK:0≤K)(f:E4→V)(h:∀ x∈coast,x≠0→ContinuousAt f x) (hk:∀ (c:Side) (i:Site c),‖f (earth (grid σ i))‖ ≤ K/‖grid σ i‖):
     Tendsto (fun c:Side=>∑ i:Site c, (beamH c^4) • f (earth (grid σ i))) atTop (𝓝 (∫ x in coast,f x)):=by
   classical
   simp_rw [← (wing_grants f ..).2, ← integral_indicator hollow.measurableSet]; apply tendsto_integral_filter_of_dominated_convergence (sky K) _ _ _ (oversees σ f h)
   exact Eventually.of_forall fun n=> (wing_grants ..).1.aestronglyMeasurable
   exact Eventually.of_forall fun n=> (show ∀ᵐ x:E4,x ≠0 from compl_mem_ae_iff.mpr (measure_singleton _)).mono fun x hx=> wing_cost hK _ n f (hk n) x hx
   exact sky_i K
lemma pole_tax (σ:Bool): ∃ C:ℝ,0 ≤ C ∧ ∀ (c:Side), ∑ i:Site c, beamH c ^ 4 / ‖grid σ i‖ ≤ C:=by
    let f:E4→ℝ:= fun p=> ‖(ix p:Axis→ℝ)‖⁻¹
    have he {p:Momentum}(h:Next.Free.physical p): ‖ix (earth p)‖=‖p‖:=by
       have he i : ‖ix (earth p) i‖=‖p i‖:=by rw [← Complex.norm_real]; rw [show (↑(ix (earth p) i):ℂ)=p i from inland h i]
       exact le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> (he i).trans_le (norm_le_pi_norm _ _)) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> (he i).symm.trans_le (norm_le_pi_norm _ _))
    have hx {c:Side}(p:Site c): f (earth (grid σ p))= ‖grid σ p‖⁻¹:= by unfold f; rw [he (cubic ..).1]
    let C:=sky 1; refine ⟨∫ x,C x, integral_nonneg (sky_pos zero_le_one), fun c=>?_⟩
    simp_rw [div_eq_mul_inv,← hx]; refine le_trans (b:=∫ x,wing c σ f x) (le_of_eq (by rw [(wing_grants ..).2]; rfl)) (integral_mono_ae (wing_grants ..).1 (sky_i 1) ?_);
    have hN x (h:x≠0): ‖wing c σ f x‖ ≤ C x:=wing_cost zero_le_one σ c f (fun i=> by rw [hx]; simp) x h
    filter_upwards [show ∀ᵐ x:E4,x ≠0 from compl_mem_ae_iff.mpr (measure_singleton _)] with x hx; exact (le_abs_self _).trans (hN x hx)
end YM.Bank.Pap
#print axioms YM.Bank.Pap.follows
#print axioms YM.Bank.Pap.pole_tax
