import YM.MassiveBridge.Mantle

/-!
# Conditional Euclidean to Wightman **massive Goal** bridge

No translation across registers, use the same `Fields.W`. Uses System and
Content (for rotations & level exhaustion), Euclidean incl Slabs, not Ward identities,
not Scaling and not Basis comparisons; in particular applicable equally to
any kernel in Decomposes which has one-ground OS vacuum. `Continuation.Produces`
alone works already without phase purity (see `continuation`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter MeasureTheory Measure
open Boundary hiding Fields Surface Soil Scroll Waves Letter Sentence Action Outfield
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius
variable {Q:Sequence}{P:Calibration Q}{F:Fields}{S:F.Kernel}{B:Bases F}{T:Momentum F}
lemma soars (E:F.System P) (H:B.Content P T) (e:Fields.Euclidean S) {C:Chamber S timeAxis}
    (h:C.UniqueHeat): ∃ R: Reconstruction F,R.Theory S:=by
  obtain ⟨K⟩:= Spinor.all E H
  obtain ⟨A⟩:=spread_ready C e E.increases E.exhaustive
  obtain ⟨B,Y,W,v,-,-,he,hP,hW⟩:=opens e E.exhaustive A
  obtain ⟨O⟩:=outfield v he hW
  obtain ⟨G,hG⟩ := Surface.Aurora.supplies (D:=pad) (Surface.tents Y E e K W he hW hP) he hP hW
  let Z : Soil W:= Classical.choice (Kernel.host O.safe)
  obtain ⟨X,hX⟩:= Z.mobilize K (W.transforms K E e he hW hP) (W.strong K E)
  obtain ⟨i,hi⟩:= daylight K Z O X hX
  let R : Reconstruction F := {
    reading:= Y.system W
    spin:=K.spin
    space:=Z.H
    D:=Z.land
    Ω:=Z.seed []
    translation:= X.orbit
    spectrum:= X.orbit.P
    U:= X.U
    φ:=Z.starter W.symbol }
  have hj (v:Sentence F): R.vector v=Z.seed v:=by
    induction v with
    | nil=> rfl
    | cons a v IH=> change Z.beginsOp a (R.vector v)=_; rw [IH,Z.actual]
  have hp (v:Sentence F): (R.vector v).val=Z.plant v:=by rw [hj]; rfl
  have ht (p:RealSpin)(b:E4)(v:Z.H): R.T p b v=X.V (p,b) v:= X.returns (p,b) v
  have hT (p:RealSpin)(b:E4)(x:Z.land): R.T p b x.val∈ Z.land:=by rw [ht]; exact Z.domain K X hX (p,b) x
  refine ⟨R,⟨K.lives,K.continuous_spin,?_,K.spatial,K.boost,K.conjugate,K.parity,K.graded, Z.omega_norm (O.soak e),?_,Z.whole,?_,?_,?_,?_,hT, ?_, X.orbit.total,X.spectrum hi, X.only hi h, Y.produces W he hW, ?_, fun x z=> Z.usable W.cam x z, fun x f u v=> Z.flipped (x,f) u v, Z.faithful E e he hG, ?_, Z.derivative e he hW hG, Z.scalarUnit E e he hW⟩⟩
  · intro p q z; rw [map_mul]; rfl
  · let J:Z.H →ₗᵢ[ℂ] C.H:=⟨i.toLinearMap,hi.scale⟩
    have := C.separable E e
    have := UniformSpace.secondCountable_of_separable C.H.space
    have := J.isometry.isEmbedding.secondCountableTopology
    change TopologicalSpace.SeparableSpace Z.H
    infer_instance
  · simp_rw [hp]; change LinearMap.range _=_; exact Finsupp.range_linearCombination ℂ
  · intro x; simp_rw [ht]; exact X.strong x
  · intro u v p q x; simp_rw [ht]; rw [← ContinuousLinearMap.comp_apply, ← X.follow]; rfl
  · intro u p; rw [ht]; exact hX [] _
  · intro p b v f x
    have h : (⟨R.T p b x.val,hT p b x⟩:R.D)=(⟨X.V (p,b) x.val,Z.domain K X hX (p,b) x⟩:R.D):=Subtype.ext (ht p b _)
    rw [h,ht]; exact Z.covariance K X hX (p,b) v f x
  · intro n u f
    rw [hp]; exact (Z.measure [] _).trans (expect_ofFn W _)
  intro x y p q H g f d hf v
  exact LinearMap.congr_fun (Z.local_op E e K he hW hP x y p q H g f d hf) v
#print axioms soars
end YM.Massive.Bridge
