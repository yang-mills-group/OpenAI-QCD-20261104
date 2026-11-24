import YM.QCD.Beam.Base
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Density
/-! # extend Beaches/Buoy measure to held Grassmann tests -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F)

def patchK (Ñ : ChartRatio G) := Metric.ball (0:G.Color) Ñ.radius
def nativeK (P : ChartRatio G) (a : G.Color) := ENNReal.ofReal (P.scale * P.J a)
def localPK (V : G.El) (P : ChartRatio G) := (fun z : G.Color=> G.lieExp z*V) '' patchK P
def capPK (Ñ : ChartRatio G) := Set.univ.pi fun i : X.Signal => localPK (replica S.ratio X.V i.1.1) Ñ

lemma exposingK {P : ChartRatio G} (h : LocalRatio P) (V : G.El) :
    MeasurePreserving (fun a => G.lieExp a * V)
      ((volume.restrict (patchK P)).withDensity (nativeK P)) (G.probHaar.restrict (localPK V P)) := by
  let L := MeasurableEquiv.mulRight V
  have hp : MeasurePreserving L G.probHaar G.probHaar := measurePreserving_mul_right _ _
  have hf : MeasurePreserving G.lieExp ((volume.restrict (patchK P)).withDensity (nativeK P))
      (G.probHaar.restrict (G.lieExp '' patchK P)) := ⟨G.lieExp_cont.measurable,h.actual⟩
  have hk := L.restrict_map G.probHaar (localPK V P)
  rw [hp.map_eq] at hk
  have he : localPK V P = L '' (G.lieExp '' patchK P) := Set.image_comp L G.lieExp _
  have hx : MeasurePreserving L (G.probHaar.restrict (G.lieExp '' patchK P)) (G.probHaar.restrict (localPK V P)) := by
    rw [hk, he,L.injective.preimage_image]; exact ⟨hp.measurable,rfl⟩
  exact hx.comp hf

def rangePK (Ñ : ChartRatio G) := Set.univ.pi fun _ : X.Signal => patchK Ñ
def expandPK (a : X.Signal→G.Color) := (fun i : X.Signal=> G.lieExp (a i)*replica S.ratio X.V i.1.1)

lemma expansionK {Ñ : ChartRatio G} (h : LocalRatio Ñ) : MeasurePreserving X.expandPK
    ((volume.restrict (X.rangePK Ñ)).withDensity (fun y => ∏ i : X.Signal, nativeK Ñ (y i)))
    (X.stages.restrict (X.capPK Ñ)) := by
  let μ : Measure G.Color := volume.restrict (patchK Ñ)
  have hm : volume.restrict (X.rangePK Ñ)=Measure.pi fun _ => μ := Measure.restrict_pi_pi ..
  haveI : SigmaFinite μ := by unfold μ; infer_instance
  have hv : Measurable (nativeK Ñ) := (measurable_const.mul h.borel).ennreal_ofReal
  haveI : SigmaFinite (μ.withDensity (nativeK Ñ)) := SigmaFinite.withDensity_ofReal _
  rw [hm, Work.F05.piDensity (fun _ : X.Signal=> μ) (fun _=>nativeK Ñ) (fun _=>hv),stages,capPK,Measure.restrict_pi_pi]
  exact measurePreserving_pi _ _ fun i : X.Signal=> exposingK h (replica S.ratio X.V i.1.1)

lemma regainsK (u) (i : X.Signal) : X.shifted u i.val=u i := by
  change (if h : X.Hot i.1.1 then u _ else _ )=_; exact dif_pos i.2
lemma expendK (a : X.Signal→G.Color) : X.view (X.tune a) = X.shifted (X.expandPK a) := by
  funext i; by_cases h : X.Hot i.val
  · rw [show X.shifted (X.expandPK a) i = X.expandPK a ⟨i,h⟩ from X.regainsK _ ⟨i,h⟩,view, if_pos h,increment, tune, dif_pos h]; rfl
  rw [view, if_neg h]; symm
  change (if hh : X.Hot i.val then _ else X.Y i)=_; exact dif_neg h

variable (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)

include K hk in
lemma shoresideK (l : Finset ℕ)(Cz : F.Slice G→ℝ)(hC : Measurable Cz) :
    (∫ u,X.tangible R W (X.shifted u) l*Cz (X.shifted u) ∂X.stages)=∫ a : X.Signal → G.Color,X.inward R Q.table W o.a l (X.tune a)*Cz (X.view (X.tune a)) := by
  let P' := Q.table; have h := Q.table_exists
  have hb := K.laws.data; have hh := hb.covers; rw [← hb.funds.length_eq] at hh
  have hc := mul_pos o.large hb.room.fiery
  have hΔ : 2*o.a*X.t < P'.radius := by dsimp only [Coat.t,P']; nlinarith only [hc,hh]
  let s := X.capPK Q.table
  let t := X.rangePK Q.table
  let f (u) := X.tangible R W u l
  have hX : MeasurableSet t := MeasurableSet.univ_pi (fun i => Metric.isOpen_ball.measurableSet)
  have he (u : F.Slice G) (hf : f u≠0) (i : X.Signal) : ∃ v∈patchK P', ‖v‖≤o.a*X.t ∧
        (u i.val)=G.lieExp v*replica S.ratio X.V i.val.val := by
    rw [← F.off_tree u i.val]; exact X.licenses _ K hk hf _ i.2
  have hg z (hz : z ∉ s) : f (X.shifted z)=0 := by
    by_contra hp; apply hz; intro i _; obtain ⟨v,hv,-,he⟩ := he _ hp i
    exact ⟨v,hv, he.symm.trans (regainsK ..)⟩
  let g (a : X.Signal→G.Color) := X.inward R P' W o.a l (X.tune a)
  let ν (u : X.Signal → G.Color) := ∏ i : X.Signal,nativeK P' (u i)
  have hM : Measurable ν := Finset.measurable_fun_prod _ fun i _=>
    ((show Measurable (nativeK P') from (measurable_const.mul h.borel).ennreal_ofReal).comp (measurable_pi_apply i))
  have hW a (i : X.Signal) : X.tune a i.val.val=a i := dif_pos i.2
  have ht (a) (ha : a ∈ t) : (ν a).toReal • f (X.shifted (X.expandPK a))=g a := by
    rw [← X.expendK]; unfold g inward
    by_cases hi : f (X.view (X.tune a))=0
    · change _=f _ * _ * _ * _; rw [hi]; simp
    have hf (i : X.Signal) : X.cone o.a (X.tune a) i.val.val=1 := by
      obtain ⟨v,hv,hk,hy⟩ := he _ hi i
      rw [X.expendK,X.regainsK] at hy
      apply X.premiere (a:=o.a) hc
      rw [hW a i,h.inject (ha i (Set.mem_univ i)) hv (mul_right_cancel hy)]; exact hk
    have hR (i : X.Signal) : Real.exp (X.gentry P' o.a (X.tune a) ((X.advance i).val))=P'.J (a i) := by
      rw [show (X.advance i).val=i.1.1 from rfl, (X.doorway (a:=o.a) hc _ _ (by rw [hf]; norm_num) h hΔ).2,hW]
    unfold ν enforce; rw [Real.exp_sum,ENNReal.toReal_prod]
    have hF : Fintype.card X.Signal = X.tier.card := (Fintype.card_congr X.advance).trans (Fintype.card_coe _)
    have hG i : (nativeK P' (a i)).toReal=P'.scale*P'.J (a i) := ENNReal.toReal_ofReal (mul_nonneg h.scale.le (h.pos (a i) (ha i (Set.mem_univ _))).le)
    have hv (F : Bond _ → ℝ) : ∏ i∈X.tier,F i=∏ i : X.Signal,F (X.advance i) := by
      rw [← Finset.prod_coe_sort X.tier, X.advance.prod_comp (fun i=> F i.val)]
    simp_rw [hv,hG,hR, prod_mul_distrib,prod_const,card_univ,hF]
    change _= f _*_*(∏ i : X.Signal,P'.J (a i))*(∏ i : X.Signal,X.cone o.a (X.tune a) i.val.val); simp_rw [hf]; simp only [prod_const_one,smul_eq_mul,mul_one]; ring
  have hy (a) (ha : a ∉ t) : g a=0 := by
    by_contra hp
    have he : X.enforce o.a (X.tune a) X.tier≠0 := right_ne_zero_of_mul hp
    apply ha; intro i _
    rw [← hW a i]; exact (X.doorway hc _ _ (fun hm=> he (prod_eq_zero (X.advance i).2 hm)) h hΔ).1
  have hr := X.expansionK h
  have hg' z (hz : z ∉ s) : f (X.shifted z)*Cz (X.shifted z)=0:=by rw [hg z hz,zero_mul]
  have hy' a (ha : a ∉ t) : g a*Cz (X.view (X.tune a))=0:=by rw [hy a ha,zero_mul]
  let F' z:=f (X.shifted z)*Cz (X.shifted z)
  change (∫ u,F' u ∂X.stages)=(∫ a : X.Signal→G.Color,g a*Cz (X.view (X.tune a)))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f:=F') hg', ← setIntegral_eq_integral_of_forall_compl_eq_zero hy']
  have hm : Measurable (X.shifted) := X.shore.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hM' : Measurable F' := ((X.tangibleB l K.laws.intake hb.W_pos).mul hC).comp hm
  rw [← hr.map_eq,integral_map hr.measurable.aemeasurable hM'.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hM (ae_of_all _ fun i => lt_top_iff_ne_top.mpr (ENNReal.prod_ne_top (by intro; simp [nativeK])))]
  refine setIntegral_congr_fun hX fun a ha=> ?_
  change (ν a).toReal • F' _= _; unfold F'; rw [← ht a ha,X.expendK a]; simp only [smul_eq_mul]; ring
theorem siteK (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K) (l : Finset ℕ)(Ck: F.Slice G→ℝ)(hC:Measurable Ck) :
    (∫ u,X.tangible R W (X.shifted u) l * Ck (X.shifted u) ∂X.stages)=∫ z, X.ticketK R W o.a Q.table z l * Ck (X.view (X.liftA R.beta z)):= by
  rw [X.shoresideK K hk l Ck hC]; symm
  let g := gStep R.beta; have hg : 0<g := by unfold g gStep; have := K.laws.intake.positive; positivity
  let p := X.arised.card; let h:=Units.mk0 _ hg.ne'
  let f (i) := X.inward R Q.table W o.a l i * Ck (X.view i)
  let D : (X.Speck→ℝ) ≃ᵐ( X.Signal→G.Color) := (blast h (fun i => X.μ i.val.1 i.val.2)).trans X.tunes
  let Y (x) := f (X.tune (D x))
  have hD : MeasurePreserving D (ENNReal.ofReal (g^p) • volume) volume := by
    unfold D p; rw [X.arised_size]; exact X.preserves_tunes.comp (preserving_blast h hg _)
  have hM := hD.integral_comp' (fun i=> f (X.tune i))
  rw [integral_smul_measure] at hM
  simp only [ENNReal.toReal_ofReal (pow_nonneg hg.le _),smul_eq_mul] at hM
  have hv (z) : X.ticketK R W o.a Q.table z l*Ck (X.view (X.liftA R.beta z))=Y (X.partB z).1*g^p*X.comfort (X.partB z).2 := by
    let x := X.liftA R.beta z; let x':= X.tune (D (X.partB z).1)
    have hx (j) (he : X.Hot j) : x j=x' j := by
      unfold x' tune; rw [dif_pos he]; ext k
      let i:X.Speck := ⟨(j,k),he⟩
      change _= X.tunes _ _ k; rw [X.tunes_val _ i ⟨⟨j,he.1⟩,he⟩ k rfl]; rfl
    have he : X.view x=X.view x' := by
      funext i; unfold view; split <;> rename_i h
      · unfold increment; rw [hx _ h]
      rfl
    have hg : X.enforce o.a x X.tier = X.enforce o.a x' X.tier := by
      unfold enforce; apply prod_congr rfl; intro i hi; unfold cone; rw [hx _ (mem_filter.mp hi).2]
    have hd : (∑ j∈X.tier, X.gentry Q.table o.a x j)= ∑ j∈X.tier, X.gentry Q.table o.a x' j := by
      apply sum_congr rfl; intro j hj; unfold gentry cone; rw [hx _ (mem_filter.mp hj).2]
    unfold Y f inward ticketK; dsimp only
    rw [he,hg,ribbons, hd,comfort,inv_pow,Real.exp_add]; rw [X.dormant_energy, neg_div]; unfold x' g p; ring
  rw [← X.partP.symm.integral_comp' (fun z=> X.ticketK R W o.a Q.table z l*Ck (X.view (X.liftA R.beta z)))]
  simp_rw [hv,X.partB.apply_symm_apply]
  rw [← hM]; change (∫ z : ((X.Speck→ℝ) × (X.Vacant→ℝ)), Y z.1*g^p*X.comfort z.2 ∂volume.prod volume)=_
  rw [integral_prod_mul (fun i=> Y i*g^p) X.comfort, X.comfy,mul_one, integral_mul_const]; exact mul_comm ..

lemma ticketM (K : Cash W X.x μ L Q o C T R) (h : X.manifest) (hk : X.width=o.K) (k) (Y)
    (hp : Layout X.seeds Q.halo X.B Y) (hl : Contract.sealed R k) (CM: F.Slice G→ℝ)(hC:Measurable CM) :
    (∫ u,X.tangible R W (X.shifted u) k*CM (X.shifted u) ∂X.stages) = (Fintype.card S.Choices:ℝ)⁻¹ * X.levy R * X.deducted Q.table R.beta*
      ∫ z,X.summedUp R Q.table W o.a z k Y*CM (X.view (X.liftA R.beta z)) ∂X.dice := by
  let g (z) := ENNReal.ofReal (X.thetaRef z)
  have hd : X.dice = volume.withDensity g := Poll.sweep_pdf (K.laws.data.localP F X rfl hk h).sails.fullC
  have hg : Measurable g := by unfold g thetaRef dotProduct; fun_prop
  rw [X.siteK K hk k CM hC, hd, integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun _=> ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  apply integral_congr_ae; filter_upwards with z
  rw [X.consolidated k K h hk z hp hl]; unfold g; rw [ENNReal.toReal_ofReal (show 0≤ X.thetaRef _ by unfold thetaRef bell; positivity),smul_eq_mul]; ring
end YM.ConnectedActivityE6.Coat
