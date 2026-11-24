import YM.Hypnos.Spokes
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.HeadSwitch
/-! # Nested volumes and the SAME pre-step covariance with thermal tree data. Through bare probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}
open Assembly
variable (X:Coat T F)(Y: Support c)
-- release wraps
abbrev Star (F:Tree.Forest S.ratio) (G:Gauge):= FreeResolvent.Active G F
def knee (G:Gauge) (F: Tree.Forest S.ratio) (x:ℝ): Star F G≃ (JointLoad.Heir.clear S x F × G.ColorIndex) := -- binder fix
   opened G S x (bareStores S) F (notChilled S F x)
private theorem knee_eq (v:Star F G): (tube X) (knee G F X.x v)=((v.1.val),v.2):= rfl
-- exact equality of V9 materials before testing relative full
private def jo (V : Config G c):= pane (sectorW G S X.x (bareStores S) F .endpoint) (Rows.gram T X.x V X.k (shots S X.x) (bareStores S) F) 0
lemma raze : optics X 0=mirror (jo X 1):=by
   unfold optics pickedCov; rw [map_zero,field_zero]; unfold jo sectorW; rw [pane_zero]; rfl
lemma portal_e (u i:Star F G) : optics X 0 (knee G F X.x u) (knee G F X.x i)=mirror ((jo X 1).submatrix (knee G F X.x) (knee G F X.x)) u i :=by rw [raze]; rfl

structure Material (X:Coat T F)(L:Side)(H:Bed)(r:ℝ):Prop where
   ideal : ∃ α η E γ : ℝ, 0<α ∧ FreePrice (FreeResolvent.native c) (FreeResolvent.theta _ F) (FreeResolvent.treeMatrix G S F H.metric) ((jo X 1).submatrix (knee G F X.x) (knee G F X.x)) α E r γ ∧ FreeResolvent.Gap (FreeResolvent.treeMatrix G S F H.metric) η
-- eventual with same numerical
lemma polarized (G : Gauge) (P:Teller G)(L:Side)(D:Patch)(v:ℝ) :∃ R : ℝ → ℝ, Rate G L v R ∧ ∀ᶠ x :ℝ in atTop,
    ∀ {c f: Side}(S:StepData c f)(T:Tube G S),S.patch=D→ Works P L x S T→∀ H:Bed, Attached H T.up→ (H.full T.high f).transpose* H.full T.high f=H.metric.acts f → Sworn H f G →
    ∀ (F : Forest S.ratio)(X:Coat T F), X.x=x→Material X L H (R x):=by
    obtain ⟨α,η,E,γ,t,hα,hE,hγ,ht,hη,H⟩:= Assembly.freeHead G D P.bind P.top.clip P.top.width_pos P.top.paths_pos.le
    let R (x:ℝ):= E*Real.exp (-t*radiusB x); refine ⟨R,?_,?_⟩
    · apply Rate.mul_left _ E -- exact ?
      apply ((Rate.cutoff (δ:=t) ht)).compare
      filter_upwards with x; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone
      have he : (till x:ℝ)≤(radiusB x:ℝ):=by exact_mod_cast Nat.div_le_self ..
      nlinarith
    filter_upwards [ConnectedActivityE6.room G P L,H] with x hR h c f S T hx hF B hB hM hW F X he; subst x
    obtain ⟨a,b,hU,hG⟩:=hF.funds.feeds
    obtain ⟨hy,h⟩:= h.2 S T hx hF.funds.knobs (hR c f S T hF).larger hF.funds.high a hU F X.k (bareStores S) Assembly.Geometry.endpoint (notChilled S F X.x) B hB (hF.funds.high ▸ hM) hW
    exact ⟨_,η,E,γ,hα,h,hy⟩

lemma ticket {H:Bed} (h:Material X L H r) (i j: Star F G) : |optics X 0 (knee G F X.x i) (knee G F X.x j)-(FreeResolvent.treeMatrix G S F H.metric)⁻¹ i j|≤ r:=by
    obtain ⟨α,η,E,γ,hα,h,h₁⟩:=h.ideal
    rw [portal_e]; have hy:= (h.cov.rows.mono hα.le le_rfl).weighted i j; rw [FreeResolvent.Cost.weight_zero,one_mul] at hy; exact hy
-- from Malachite C.Replace.
lemma panes_native (h: Photic X u t C 2) (b:Directions G c) (hb:‖b‖≤u) (he:X.V=increment 1 b)(p:Room P S T X.x)(hf:∀ i∈Y,¬Inside i X.seeds (30*X.B))
   (i j:Eye X) (hy: (atEdge S j.1.val.val) ∈ Y) :
   |X.relating (tube X i) (tube X j) - optics X 0 i j| ≤ C*u+t:=by
    let f (b:Directions G c) := (stoneC X b).submatrix (tube X) (tube X) i j
    have hP y (hy:y∈Metric.closedBall (0:Directions G c) u) := Malachite.settled.mp (h.horizon y i j (mem_closedBall_zero_iff.mp hy))
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (f:=f) (s:=Metric.closedBall (0:Directions G c) u) (fun y hy=> (hP y hy).smooth.differentiableAt (by simp)) (fun y hy=> price_one (hP y hy) (by omega)) (convex_closedBall _ _)
      (Metric.mem_closedBall_self ((norm_nonneg b).trans hb)) (mem_closedBall_zero_iff.mpr hb)
    have hC := (Malachite.settled.mp (h.studies b hb)).nonneg
    rw [Real.norm_eq_abs,sub_zero] at hh; have hk:= hh.trans (mul_le_mul_of_nonneg_left hb hC)
    have hz:=pact X he (hf _ hy)
    rw [hz.cL p (tube X j) rfl (tube X i) (by omega)]; exact (norm_sub_le_norm_sub_add_norm_sub _ (f 0) _).trans (add_le_add hk (Control.only_price h.shade.1 le_rfl i j))

lemma enlightened {H:Bed} (h:Material X L H r) (hT: Photic X u t C 2) (b:Directions G c) (hb:‖b‖≤u) (he:X.V=increment 1 b)(p:Room P S T X.x)(hf:∀ i∈Y,¬Inside i X.seeds (30*X.B))
   (i j:Star F G) (hy:S.ratio.parent j.1.val.1∈ Y) :
   |X.relating (i.1.val,i.2) (j.1.val,j.2)-(FreeResolvent.treeMatrix G S F H.metric)⁻¹ i j|≤ C*u+t+r :=
       (norm_sub_le_norm_sub_add_norm_sub _ (optics X 0 (knee G F X.x i) (knee G F X.x j)) _).trans
         (add_le_add (panes_native X Y hT b hb he p hf (knee G F X.x i) (knee G F X.x j) hy) (ticket X h i j))
end YM.Hypnos
#print axioms YM.Hypnos.polarized
#print axioms YM.Hypnos.enlightened
