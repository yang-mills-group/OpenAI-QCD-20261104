import YM.TorusPCAC.Geometry.Pull

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Charge action descends through ALL tag branches including fallback -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Geometry.Reflection
open QCD QCD.Lat QCD.Kit QCD.Grass Lattice Wilson Finite Finset MeasureTheory Function Filter RG Revolve Ward Stencil
open scoped Matrix Topology BigOperators Kronecker Matrix.Norms.Frobenius Classical
variable {n c f : Side} {N : ℕ}
local notation "q"=>conjSU
abbrev dual : su.El→*su.El where
 toFun:=conjSU
 map_one':= su.mat_injective (by change which true (su.mat 1)=_; rw [Gauge.mat_one]; exact which_one _)
 map_mul':=fun _ _=>su.mat_injective (by rw [Gauge.mat_mul]; change which true (su.mat (_*_))=which true _ * which true _; rw [Gauge.mat_mul]; exact which_mul ..)
lemma trans_inv (U : su.El): q U⁻¹=(q U)⁻¹:= map_inv dual U
lemma trans_mul (U V : su.El): q (U*V)=q U*q V:= map_mul dual U V
lemma invol (U : su.El): q (q U)=U:=by apply su.mat_injective; ext; exact star_star _
lemma mapsV (U : su.El): su.mat (q U)=Twist (su.mat U):=rfl
lemma price (U: su.El): su.price (q U)=su.price U:=by simp only [Gauge.price,mapsV,Twist,Matrix.trace_transpose,Matrix.trace_conjTranspose]; rfl -- conj.re
lemma chord (U:su.El):su.chord (q U)=su.chord U:=by rw [← sq_eq_sq₀ (Gauge.chord_nonneg ..) (Gauge.chord_nonneg ..),Gauge.chord_price, price,Gauge.chord_price]
@[fun_prop] lemma continuity : Continuous q := by
  refine Topology.IsInducing.continuous_iff (?_ : Topology.IsInducing su.mat)|>.2 ?_
  · exact (Continuous.isClosedEmbedding su.continuous_mat su.mat_injective).isInducing
  simp only [Function.comp_def,mapsV]; apply continuous_matrix; intro i j; simp only [Twist,Matrix.transpose_apply,Matrix.conjTranspose_apply]; fun_prop
lemma preserve : MeasurePreserving q su.probHaar su.probHaar:=by
  haveI : (su.probHaar.map conjSU).IsHaarMeasure:= Measure.isHaarMeasure_map _ dual continuity (fun i=>⟨_,invol i⟩) (by rw [cocompact_eq_bot]; exact tendsto_bot)
  refine ⟨continuity.measurable, Eq.symm ((Measure.haarMeasure_eq_iff su.allElements _).mpr ?_)⟩
  change (Measure.map conjSU _) Set.univ=1; rw [Measure.map_apply continuity.measurable MeasurableSet.univ]; simp
@[fun_prop] lemma grid_cts : Continuous (conjGrid : Grid n → Grid n) := by unfold conjGrid; fun_prop
lemma grid_preserve : MeasurePreserving (conjGrid : Grid n→ Grid n) (prior su n) (prior su n) :=measurePreserving_pi _ _ (fun (_ : Edge (Site n))=>preserve)

variable {R:Type*} [AddCommGroup R] [One R]
lemma roadmap (U:Links R su.El) (x:Four R)(w) : travel (q ∘ U) x w=q (travel U x w):=by
 induction w generalizing x with
 | nil=> exact (map_one dual).symm
 | cons a w ih=> rw [travel,ih,travel,trans_mul,Step.read,Step.read]; split <;> rfl
lemma faces (U:Links R su.El) (p:Face R): faceValue (q ∘ U) p=q (faceValue U p):=roadmap ..
lemma energy_alt (β : ℝ) (U : Grid n): bare β (conjGrid U)=bare β U:=by simp_rw [bare,energy,conjGrid,faces, price]

variable (J:Patch) (K:KernelChoices)
variable (U:CoverConfig su) (Y:J.Connector su)
local notation "u'"=> q ∘ U
local notation "y'"=> q ∘ Y
lemma aligned (h:J.Frame su)(x y:J.Points) (l:Lattice.Order) : J.via (q∘ h) u' x y l=q (J.via h U x y l):=by simp only [Patch.via,trans_mul,trans_inv,comp_apply,roadmap]
lemma value (h:J.Frame su):J.score u' (q ∘ h)=J.score U h:=by simp_rw [Patch.score,aligned,price]
lemma pillars (t):J.axial u' t=q ∘ J.axial U t:=funext (fun _=> roadmap ..)
lemma open_min : J.usesMin K u' ↔ J.usesMin K U:=by simp_rw [Patch.usesMin,pillars,aligned,chord]
lemma sprint (h: J.Frame su):q∘ (q∘h)=h:=funext fun i=>invol (h i)
lemma selected (hg:J.Branches K su)(hp:J.usesMin K U): J.selected u'=q ∘ J.selected U:=by
 apply (hg.frame_unique u' ((open_min ..).mpr hp)).unique (J.min_exists _).choose_spec
 have ⟨hh,hw⟩:= (J.min_exists U).choose_spec; refine ⟨?_,fun H hb=>?_⟩
 · rw [comp_apply, show J.selected U J.center=1 from hh]; exact map_one dual
 rw [value]; refine (hw (q∘ H) (by rw [comp_apply,hb]; exact map_one dual)).trans_eq ?_; rw [← value J U (q ∘ H), sprint]
lemma frame (hg:J.Branches K su) (t:J.FrameTag): J.frame K u' t=q ∘ J.frame K U t:=by
 by_cases hp:J.usesMin K U
 · rw [Patch.frame,if_pos ((open_min ..).mpr hp),selected J K U hg hp,Patch.frame,if_pos hp]
 rw [Patch.frame,if_neg (mt (open_min ..).mp hp),Patch.frame,if_neg hp]; funext i; simp only [pillars,comp_apply,trans_inv,trans_mul]
lemma eligible : J.eligible K u'=J.eligible K U:=by
 have ha t:J.axialCost u' t=J.axialCost U t:=by simp_rw [Patch.axialCost,pillars,comp_apply,← trans_inv,← trans_mul,chord]
 have hb : J.facesum u'=J.facesum U:=by simp_rw [Patch.facesum,faces,chord]
 unfold Patch.eligible; simp only [ha,hb]
lemma frame_cost (t:J.FrameTag) : J.frameMass K u' t=J.frameMass K U t:=by unfold Patch.frameMass; rw [eligible]; exact if_congr (open_min ..) rfl rfl
lemma bond (T:su.El): J.bondCost y' (q T)=J.bondCost Y T:=by simp only [Patch.bondCost,comp_apply,← trans_inv,← trans_mul,price]
lemma fees : J.bondCost y' (J.best y') =J.bondCost Y (J.best Y):=by
 have he:= (J.bond_min y').choose_spec (q (J.best Y))
 rw [bond] at he
 apply he.antisymm; refine ((J.bond_min Y).choose_spec (q (J.best y'))).trans_eq ?_; rw [← bond J Y (q (J.best y')),invol]; rfl
lemma best (hg:J.Branches K su)(h:J.usesBest K Y): J.best y'=q (J.best Y) :=by
 refine (hg.predictor_unique _ (by unfold Patch.usesBest; rw [fees]; exact h)).unique (J.bond_min y').choose_spec (fun i=>?_)
 rw [bond,← fees J Y]; exact (J.bond_min y').choose_spec _
lemma predicts (hg:J.Branches K su) (r): J.predict K y' r=q (J.predict K Y r):=by
 have he : J.usesBest K y' ↔ J.usesBest K Y:=by simp only [Patch.usesBest,fees]
 by_cases h:J.usesBest K Y
 · rw [Patch.predict,if_pos (he.mpr h),best J K Y hg h,Patch.predict, if_pos h]
 rw [Patch.predict,if_neg (mt he.mp h),Patch.predict,if_neg h]; rfl
lemma predicts_price (r): J.predictorMass K y' r=J.predictorMass K Y r:=by simp [Patch.predictorMass,Patch.usesBest,fees]

variable (D : StepData c f) (L : Grid f) (h : D.patch.Branches D.kernel su)
local notation "X"=> conjGrid L
lemma expanded (x : Site f) : expandAt x X=q∘ expandAt x L:=rfl
include h
lemma conduct (t) (e) : D.connector X t e=q ∘ D.connector L t e :=by
 funext x; unfold StepData.connector StepData.frames; rw [expanded,frame _ _ _ h, roadmap,expanded,frame _ _ _ h]; simp only [comp_apply,trans_mul,trans_inv]
lemma noise (β : ℝ)(V : Grid c) : D.density β X (conjGrid V)=D.density β L V:=by
 unfold StepData.density; simp_rw [StepData.noise,StepData.likelihood,StepData.prediction, conduct D L h, predicts _ _ _ h, expanded, frame_cost,predicts_price,conjGrid,comp_apply,← trans_inv,← trans_mul,StepData.penaltyWeight,price]
end YM.TorusPCAC.Geometry.Reflection

#print axioms YM.TorusPCAC.Geometry.Reflection.grid_preserve
#print axioms YM.TorusPCAC.Geometry.Reflection.energy_alt
