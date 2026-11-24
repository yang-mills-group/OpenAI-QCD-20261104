import YM.Kly.Sphere
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
open TopologicalSpace Pointwise
open scoped Pointwise
private lemma monoid_sep {X : Type*} [Monoid X] [TopologicalSpace X] [ContinuousMul X]
    {s : Set X} (h : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (Submonoid.closure s : Set X) := by
  have hp (n : ℕ) : TopologicalSpace.IsSeparable (s ^ n) := by
    induction n with
    | zero =>
      rw [pow_zero]; exact (countable_singleton (1 : X)).isSeparable
    | succ n ih =>
      rw [pow_succ, ← image_mul_prod]; exact (ih.prod h).image continuous_mul
  refine (TopologicalSpace.IsSeparable.iUnion hp).mono ?_
  intro x hx
  change x ∈ Submonoid.closure s at hx
  induction hx using Submonoid.closure_induction with
  | mem x hx => exact mem_iUnion.mpr ⟨1, by simpa using hx⟩
  | one => exact mem_iUnion.mpr ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨n+m, by rw [pow_add]; exact mul_mem_mul hn hm⟩

private theorem comp_cont (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] :
    ContinuousMul (X →L[ℂ] X) := inferInstance
private theorem op_metrizable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] :
    PseudoMetrizableSpace (X →L[ℂ] X) := inferInstance

include E H Y P
lemma cloudy : TopologicalSpace.IsSeparable P.generators:=by
    classical
    let B(d:ℕ): Module.Basis (Fin (Module.finrank ℂ (F.level d))) ℂ ↥(F.level d):= by haveI:= E.finite d; exact Module.finBasis ℂ (F.level d)
    let J(d:ℕ):= Fin (Module.finrank ℂ (F.level d)); let f(n d:ℕ)(p:Fin n→J d) (j:Fin n):F.W := ((B d) (p j)).val -- B untyped problem
    let D(n d:ℕ)(p:Fin n→J d): Set V.VacuumOp:= mapsL P (f n d p) H '' conf n
    let W:= ⋃ n:ℕ, ⋃ d:ℕ, ⋃ p, D n d p
    have hw: TopologicalSpace.IsSeparable W:= IsSeparable.iUnion fun n=> IsSeparable.iUnion fun d=> IsSeparable.iUnion fun p=> (show ContinuousOn (mapsL P (f _ _ p) H) (conf n) from fun x hx=>(plated P H Y E x (f _ _ p) hx).continuousAt.continuousWithinAt).isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace _)
    have hp(n:ℕ)(x:Points n)(hx:x∈conf n)(v:Fin n→ F.W) : mapsL P v H x∈ Submodule.span ℂ W:=by
          obtain ⟨d,u,ht⟩:= Rotate.cover_cap E v; rw [ht]; let D': MultilinearMap ℂ (fun _:Fin n=> ↥(F.level d)) V.VacuumOp:= (P.algebra.subtype.toAlgHom.toLinearMap.compMultilinearMap (meter P H n x)).compLinearMap (fun _=>(F.level d).subtype); change D' u ∈ _; rw [Multilabel.expansion (fun _=> B d)]; apply Submodule.sum_mem; intro j hj; apply Submodule.smul_mem
          exact Submodule.subset_span (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨j,x,hx,rfl⟩⟩⟩)
    apply (show TopologicalSpace.IsSeparable (Submodule.span ℂ W:Set V.VacuumOp) from hw.span).mono
    rintro _ ⟨w,d,hd,rfl⟩; have ht:= hp w.length (positions w) hd.2.1.1 (tokens w); change (P.slot w d hd).val∈ (Submodule.span ℂ W:Set V.VacuumOp); rw[← spots P H hd]; change (meter P H _ _ _).val∈ _ at ht; rw [mAt P H (positions w) hd.2.1.1] at ht
    apply Eq.subst (motive:=fun f:P.algebra=> f.val∈ _) (?_ : lineP P H (positions w) hd.2.1.1 (tokens w)=M P w hd.2.1.1) ht; change M P (realize (tokens w) (positions w)) ((realized ..).mpr hd.2.1.1)=_; congr 1; exact knit _
lemma team : ∃ u:ℕ→P.algebra,DenseRange u :=by
    let sep:=cloudy P H Y E; have hU : TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ P.generators : StarSubalgebra ℂ V.VacuumOp) : Set V.VacuumOp) := by
       haveI : ContinuousMul V.VacuumOp := comp_cont ↥V.D
       change TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ P.generators).toSubalgebra.toSubmodule : Set V.VacuumOp)
       rw [StarAlgebra.adjoin_eq_span, ← image_star]
       exact (monoid_sep (sep.union (sep.image continuous_star))).span
    have hall: TopologicalSpace.IsSeparable (P.algebra : Set V.VacuumOp):= hU.closure
    haveI : PseudoMetrizableSpace V.VacuumOp := op_metrizable ↥V.D
    haveI : SeparableSpace ↥P.algebra:= hall.separableSpace
    exact ⟨denseSeq _,denseRange_denseSeq _⟩
omit P H Y E
open MeasureTheory OS.Ground Measure WeakDual Spectral
private lemma receives_ {A : Type} [CommCStarAlgebra A] (H : Hilbert) (p : A →⋆ₐ[ℂ] H.Op) (w : H) (hw : ‖w‖=1)
    (u : ℕ → A) (hu : DenseRange u) (ht : ∀ i : A, p i w=0 → i=0) : ∃ R : Panes A, R.Shines H p w ∧ ∀ f:R.X→ℂ,Continuous f→∃ i:A,f=fun x=>R.character x i := by
  classical
  let X := Theta (X := A)
  letI : MetrizableSpace X := tiny u hu
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MeasurableSpace X := borel _; letI : BorelSpace X := ⟨rfl⟩
  let P : Rep.CC X →⋆ₐ[ℂ] H.Op := p.comp ((gelfandStarTransform A).symm : _ →⋆ₐ[ℂ] _)
  let V : Panes A := { X := X, μ := Rep.sees P w, character := view }
  have hp i : P (gelfandStarTransform A i)=p i := congr_arg p ((gelfandStarTransform A).symm_apply_apply _)
  refine ⟨V,⟨?_,?_,bij,view_cont,mark_cont,?_⟩,?_⟩
  · apply isProbabilityMeasure_iff_real.mpr
    change (Rep.sees P w).real _=1
    rw [Rep.size,hw,one_pow]
  · refine supports H P w ?_
    intro x hx
    obtain ⟨i,rfl⟩ := (gelfandStarTransform A).surjective x
    change P (gelfandStarTransform A i) w=0 at hx; rw [hp] at hx
    change (gelfandStarTransform A i)=0; rw [ht i hx,map_zero]
  · intro i
    have h := Rep.pairings P w (gelfandStarTransform A i)
    rw [hp] at h; exact h
  intro f hx; obtain ⟨z,h⟩:= (gelfandStarTransform A).surjective ⟨f,hx⟩; exact ⟨z,funext fun i=> congr_arg (fun q:ContinuousMap X ℂ=>q i) h.symm⟩


local notation "Ω"=>P.algebra
noncomputable def dome(V:Chamber S timeAxis):Hilbert:=⟨↥V.D⟩ -- constructor
variable(h:∀ x:F.W,F.adj timeAxis (F.parity x)= F.parity (F.adj timeAxis x))
include P E Y R H h
lemma ascent :∃ A : Panes Ω, A.Shines (dome V) P.algebra.subtype V.omega0∧∀ f:A.X→ℂ,Continuous f→∃ i:Ω,f=fun x=> A.character x i:=by
    obtain ⟨u,hu⟩:= team P H Y E; haveI : IsClosed (P.algebra : Set V.VacuumOp) := isClosed_closure
    letI : CommCStarAlgebra P.algebra := {
       (StarSubalgebra.cstarAlgebra P.algebra) with mul_comm := possible P H Y R (E.reflected _) E.folded h }
    exact receives_ (dome V) (show P.algebra →⋆ₐ[ℂ] (dome V).Op from P.algebra.subtype) (show (dome V) from V.omega0) (nil_norm V.GNS Y) u hu (fun i=>tooth P H Y R E h i)
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.ascent
