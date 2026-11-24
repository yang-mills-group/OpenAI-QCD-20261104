import YM.Kly.Stow
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
variable (T: FlavorTorus→* (V.H≃ₗᵢ[ℂ] V.H))(hT:∀ p:FlavorTorus,∀ v,T p (V.GNS.plant v)=V.GNS.plant (boat p v))
local notation "Θ"=> P.algebra
variable (p:FlavorTorus)
noncomputable abbrev lineG : V.H.Op:= (T p).toContinuousLinearEquiv.toContinuousLinearMap
include hT
lemma walks (v:V.H)(d:ℝ≥0): T p (V.flow.E d v) = V.flow.E d (T p v):=by
    let L:= lineG T p; apply DFunLike.congr_fun (f:=L.comp (V.flow.E d)) (g:=(V.flow.E d).comp L); refine V.GNS.by_bud fun j=>?_ ; change T p (V.flow.E d _)= V.flow.E d (T p _); rw[hT, ← V.atBirth,hT, ← V.atBirth, teaB]
lemma gravid (x:↥V.D): T p x.val∈ V.D:= (V.flow.fixed _).2 fun d=>by rw [←walks T hT p, (V.flow.fixed _).1 x.property]
noncomputable def hartK : FlavorTorus→*(V.D≃ₗᵢ[ℂ] V.D):=by
    let v(p:FlavorTorus): V.D→ₗᵢ[ℂ] V.D:=by
         refine { toFun:=fun x=> ⟨_, gravid T hT p x⟩,map_add':=fun x y=> Subtype.ext ((T p).map_add ..),map_smul':=fun c x=> Subtype.ext ((T p).map_smul ..), norm_map':=fun x=> (T p).norm_map x.val }
    have he(p:FlavorTorus): Surjective (v p):= fun x=>⟨v p⁻¹ x,Subtype.ext (by change T p _=x.val; rw [show ((v p⁻¹ x):V.H)=T p⁻¹ x.val from rfl,map_inv]; exact (T p).apply_symm_apply _)⟩
    let W(p:FlavorTorus):= LinearIsometryEquiv.ofSurjective (v p) (he p); refine ⟨⟨W,?_⟩,?_⟩; · apply LinearIsometryEquiv.ext; intro x; apply Subtype.ext; change T 1 _= x.val; rw [map_one]; rfl
    intro p q; apply LinearIsometryEquiv.ext; intro x; apply Subtype.ext; change T (p*q) _= T p (T q x.val); rw [map_mul]; rfl
local notation "J" => hartK T hT
lemma earns (x:V.D): (J p x).val=T p x.val:=rfl
lemma chairP : J p V.omega0=V.omega0:=Subtype.ext (by rw[earns]; apply (hT p (air _)).trans; rw [boat_start]; rfl)
lemma tracks(r:V.H): (J p) (V.D.orthogonalProjectionOnto r)= V.D.orthogonalProjectionOnto (T p r):=by
      apply ext_inner_left ℂ; intro x; obtain ⟨v,rfl⟩:= (J p).surjective x; rw[LinearIsometryEquiv.inner_map_map, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,earns]; exact (LinearIsometryEquiv.inner_map_map ..).symm
omit hT
lemma sailsF (b:Cluster F)(d:ℝ≥0)(hb:Slab t₀ d b): Slab t₀ d (jug p b):=by
      refine ⟨hb.1,jar p ⟨_,hb.2.1⟩,?_⟩; intro i h; obtain ⟨u,hu,rfl⟩:=List.mem_map.mp h; exact hb.2.2 u hu
include hT
lemma ende (v: Cluster F)(d:ℝ≥0)(hv:Slab t₀ d v) (x:V.H): T p (P.place d v x)= P.place d (jug p v) (T p x):=by
      apply DFunLike.congr_fun (f:=(lineG T p).comp (P.place d v)) (g:=(P.place d (jug p v)).comp (lineG T p)); refine V.GNS.by_bud fun x=>?_ ; change T p (P.place _ _ (V.GNS.plant x))=_; rw[P.reads hv,hT]; change _=P.place d (jug p v) (T p (V.GNS.plant _)); rw [hT, P.reads (sailsF p v d hv)]; apply congr_arg; apply Subtype.ext; change jug p (v++carry x.val _) = _ ++ carry (jug p _) _; simp only[jug,List.map_append,carry,List.map_map]; rfl
noncomputable def sky {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E](p:E≃ₗᵢ[ℂ]E): (E→L[ℂ] E)→⋆ₐ[ℂ](E→L[ℂ]E):=by
     let L:=p.toContinuousLinearEquiv.toContinuousLinearMap; let V:=L.adjoint; have hl:V= p.symm.toContinuousLinearEquiv.toContinuousLinearMap := p.adjoint_eq_symm; have hv:L* V=1:=ContinuousLinearMap.ext (fun x=> by rw [hl]; exact p.apply_symm_apply _); have he:V*L=1:= ContinuousLinearMap.ext fun x=>by rw[hl]; exact p.symm_apply_apply x
     exact { toFun:= fun x=>L*x*V,map_zero':=by simp,map_one':=by rw [mul_one,hv],map_mul':=fun x y=>by simp only [mul_assoc]; rw [← mul_assoc V L,he,one_mul],map_add':=fun x y=>by rw[mul_add,add_mul], map_star':=fun x=>by rw [star_mul,star_mul]; unfold V; rw [show L.adjoint=star L from rfl,star_star,mul_assoc], commutes':=fun x=>by rw [← (Algebra.commutes x L),mul_assoc,hv,mul_one] }
lemma sick (x:V.VacuumOp)(v:V.D): sky (J p) x v= J p (x (J p⁻¹ v)):=by rw[map_inv]; change J p (x ((J p).toContinuousLinearEquiv.toContinuousLinearMap.adjoint v))=_; rw [LinearIsometryEquiv.adjoint_eq_symm]; rfl
lemma stain (v:Cluster F)(d:ℝ≥0)(hv:Slab t₀ d v): sky (J p) (P.atom v d) = P.atom (jug p v) d :=by
     ext1 x; obtain ⟨y,rfl⟩:= (J p).surjective x; rw [sick T hT,map_inv]; change J p (P.atom _ _ ((J p).symm (J p y)))= _; rw [LinearIsometryEquiv.symm_apply_apply]; unfold Spread.atom; change J p (V.D.orthogonalProjectionOnto _)= V.D.orthogonalProjectionOnto (P.place _ _ (J p y).val); rw [earns,tracks]; apply congr_arg; exact ende P T hT p v d hv y.val
lemma grows (x :Θ): sky (J p) x.val ∈ P.algebra:=by
     let L:= sky (J p); have he:StarAlgebra.adjoin ℂ P.generators≤ P.algebra.comap L:= StarAlgebra.adjoin_le_iff.mpr fun y ⟨w,d,h,q⟩=> q ▸ (show L (P.atom w d)∈ Θ from stain P T hT p w d h ▸ (P.slot (jug p w) d (sailsF p w d h)).property)
     have hc : Continuous L:=by
          have hc: Continuous fun y:V.VacuumOp=> ((J p).toContinuousLinearEquiv.toContinuousLinearMap)*y*(J p).toContinuousLinearEquiv.toContinuousLinearMap.adjoint:= by fun_prop
          exact hc
     exact closure_minimal he (IsClosed.preimage hc (show IsClosed (P.algebra : Set V.VacuumOp) from isClosed_closure)) x.property
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.grows
#print axioms YM.Massive.Bridge.Kly.sick
#print axioms YM.Massive.Bridge.Kly.tracks
