import YM.MassiveBridge.Lifecycle

/-!
# Spectrum from WSpins motion and same-chamber intertwining

 Soil only sees tests which are limits of words; extend to the same chamber,
 preserving all translations. Faith/use from statements proven separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter MeasureTheory Measure Mink Spectral Complex
open Boundary hiding Fields Surface Soil Scroll Waves Letter Sentence Action Outfield
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius
variable {F:Fields} {S:F.Kernel} {X:Hilbert}
namespace Action
open Travel
variable (P:Action X)
def orbit : Orbit X E4 where
   translation b:= P.V (across b)
   moves x := (P.strong x).comp (continuous_const.prodMk continuous_id)
   unitary x:= P.usual _
   origin := P.one
   sends x y := by rw [←P.follow,Travel.over]

lemma inert_inv (p:RealSpin)(x:X):P.V (Travel.spin p⁻¹) (P.V (Travel.spin p) x)= x:=by
   rw [←ContinuousLinearMap.comp_apply,←P.follow,inert,inv_mul_cancel,show Travel.spin 1= Travel.stand from rfl,P.one];rfl

def U:RealSpin →* (X ≃ₗᵢ[ℂ] X) where
   toFun p:=
     { toFun:= P.V (Travel.spin p)
       map_add':= (P.V (Travel.spin p)).map_add
       map_smul':= (P.V (Travel.spin p)).map_smul
       invFun:= P.V (Travel.spin p⁻¹)
       left_inv x:= inert_inv P p x
       right_inv x:= by simpa only [inv_inv] using inert_inv P p⁻¹ x
       norm_map' x:= P.usual _ _ }
   map_one' := by
     ext x
     change P.V Travel.stand x=x
     rw [P.one];rfl
   map_mul' p q:= by
     ext x
     change P.V (Travel.spin (p*q)) x= P.V (Travel.spin p) (P.V (Travel.spin q) x)
     rw [← ContinuousLinearMap.comp_apply,← P.follow, Travel.inert] -- ?
lemma returns (p:Travel)(x:X): P.orbit.translation p.2 (P.U p.1 x)=P.V p x:=by
   change P.V (across p.2) (P.V (Travel.spin p.1) x)=_
   rw [← ContinuousLinearMap.comp_apply,← P.follow,acre]

def spaceKeep (s : Travel) : X→ₗᵢ[ℂ] X := ⟨(P.V s).toLinearMap,P.usual s⟩
lemma flavor (s : Travel) (x y : X) : inner ℂ (P.V s x) (P.V s y)=inner ℂ x y := (P.spaceKeep s).inner_map_map _ _

def μ (x : X) := P.orbit.P.diagonal x
instance (x : X) : IsFiniteMeasure (P.μ x) := P.orbit.P.finite _
lemma placed (r:RealSpin) (x:X): P.μ (P.V (Travel.spin r) x)=(P.μ x).map (Lorentz.act (Lorentz.dual r.coord)):=by
  have he (p:E4): Travel.follow (across (r.coord.act p)) (Travel.spin r)=Travel.follow (Travel.spin r) (across p) := by rw [Travel.acre,Travel.beside]
  have hm : IsFiniteMeasure ((P.μ x).map (Lorentz.act (Lorentz.dual r.coord))) := by infer_instance
  apply Measure.ext_of_charFun; ext1 b
  obtain ⟨p,rfl⟩ := r.coord.sends.surjective b
  have hx : charFun (P.μ (P.V (Travel.spin r) x)) (r.coord.act p) = charFun (P.μ x) p := by
    unfold μ; rw [P.orbit.total,P.orbit.total]
    change inner ℂ _ (P.V (across (r.coord.act p)) (P.V _ _)) = inner ℂ _ (P.V (across p) x)
    rw [← ContinuousLinearMap.comp_apply, ← P.follow,he p,P.follow]; exact P.flavor ..
  rw [Lorentz.sent,hx, charFun_apply,charFun_apply, integral_map _ _]; rotate_left
  · exact (ContinuousLinearMap.continuous _).measurable.aemeasurable
  · exact (show Continuous (fun y : E4 => Complex.exp ((↑(inner ℝ y (r.coord.act p)):ℂ)*I)) from by fun_prop).aestronglyMeasurable
  congr! 3
  simpa using (Lorentz.dual_sent (Lorentz.dual r.coord) p _).symm

/-- every direction sharpened; true spectrum not just symbols. -/
lemma south (hp : ∀ v : X, (P.μ v).support ⊆ {p : E4|0 ≤ p timeAxis}) : P.orbit.P.region coneᶜ=0 := by
  have h v : (P.μ v).support ⊆ cone := fun x hx => (Lorentz.from_half x).2 fun r => by
    obtain ⟨r,rfl⟩:= MassiveTwoEstimates.SpinGeometry.geometry.realTime r
    apply hp (P.V (Travel.spin r) v); rw [P.placed]
    apply Measure.mem_support_iff_forall _|>.mpr
    intro A hA
    obtain ⟨U,hU,hu,hA'⟩ := mem_nhds_iff.mp hA
    refine lt_of_lt_of_le ?_ (measure_mono hU)
    rw [Measure.map_apply (ContinuousLinearMap.continuous _).measurable hu.measurableSet]
    exact ((Measure.mem_support_iff_forall _).1 hx _ ((hu.preimage (ContinuousLinearMap.continuous _)).mem_nhds hA'))
  ext1 x
  apply (P.orbit.P.null_pair closed_cone.isOpen_compl.measurableSet _).mp
  exact measure_mono_null (compl_subset_compl.mpr (h x)) (measure_compl_support)
end Action

namespace Action
variable {C : Chamber S timeAxis} (P : Action X) {W : X→L[ℂ] C.H}

/-- W maps into the chamber but distinguished Vacuum AND flows proved
later/specified before projection; not arbitrary filter limits. -/
structure Intervenes (W : X→L[ℂ] C.H) (v : X) : Prop where
  scale (x : X) : ‖W x‖=‖x‖
  across (p) : W.comp (P.orbit.translation p) = (C.flow.unit.translation p).comp W
  start : W v=C.omega

lemma spectrum {w : X} (h : P.Intervenes (C := C) W w) : P.orbit.P.region coneᶜ=0 := by
  refine P.south fun x => ?_
  have he : P.μ x=C.flow.ℚmeasure.diagonal (W x) := by
    apply Measure.ext_of_charFun; ext1 i; unfold μ; rw [P.orbit.total,C.flow.joint]
    rw [← ContinuousLinearMap.comp_apply _ W,h.across i |>.symm]
    exact (LinearIsometry.inner_map_map (⟨W.toLinearMap,h.scale⟩ : X →ₗᵢ[ℂ] C.H) x _).symm
  rw [he]; exact C.flow.nonneg _

theorem only {w : X} (h : P.Intervenes (C:=C) W w) (hc : C.UniqueHeat) (x : X) (hp : ∀ i,P.orbit.translation i x=x) :
    ∃ z : ℂ,x=z • w := by
  have he : W x∈C.D := offiero _ (W x) fun t => by rw [← ContinuousLinearMap.comp_apply _ W, ← h.across, ContinuousLinearMap.comp_apply,hp]
  obtain ⟨z,H⟩ := hc ⟨W x,he⟩
  refine ⟨z,(show Injective W from (⟨W.toLinearMap,h.scale⟩ : X→ₗᵢ[ℂ] C.H).injective) ?_⟩
  rw [map_smul,h.start];exact congr_arg Subtype.val H
end Action


lemma daylight {W:Surface F} {C:Chamber S timeAxis} (K:WSpins F) (Q:Soil W) (Z:Outfield W C) (Y:Action Q.H) (h:∀ i p,Y.V p (Q.plant i)=Q.plant (K.walk p i)): ∃ U,Y.Intervenes (C:=C) U (Q.plant []) := by
  obtain ⟨U,-,hU,hu⟩ := Q.universal_embed (M:=C.H) Z.toFun Z.at_pair
  refine ⟨U,⟨hu,fun p => Q.by_bud ?_,(hU _).trans Z.vacuum⟩⟩
  intro i
  change U (Y.V _ (Q.plant i))= C.flow.unit.translation p (U (Q.plant i))
  rw [h,hU,hU,show K.walk (Travel.across p) i=shiftBy p i from ?_,Z.volume]
  unfold WSpins.walk shiftBy
  apply congrArg (fun f=> i.map f)
  funext u
  exact Prod.ext (show (K.spin 1 u.1)=_ from by simp) rfl

end YM.Massive.Bridge
