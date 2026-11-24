import YM.Rill.Vault
/-!
# Ready kernel wrappers for later reconstruction
Only Lie/Spin on top absent. Keep eventual unique calibration path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Fir Fir Set Function Filter
open UV Patria Patria.Depth Patria.Hub Needle Poised Poised.Plans Poised.Plans.Stamp
open Choir Choir.Strip HarmonyF Quilt
open scoped Topology ContDiff BigOperators Classical ComplexOrder
noncomputable def rod (C:Sequence)(φ:ℕ→ℕ):Sequence where
    R:= C.R ∘φ
    S:= C.S
    N:= C.N∘φ
    A:=fun i=> C.A (φ i)
noncomputable def res (C:Sequence)(P:Calibration C)(φ:ℕ→ℕ):Calibration (rod C φ):=⟨P.sym,P.hol,P.test,P.stencil,P.localMap,P.candidate,fun d v i=> P.mix d v (φ i),P.base⟩
variable {C:Sequence}{P:Calibration C}{K:Choir}{φ:ℕ→ℕ} {β e:ℝ}(hp:C.Path β e)(hP:P.System)(hφ:StrictMono φ)
include hp hφ
lemma acrossW : (rod C φ).Path β e:=by
    have h:=hφ.tendsto_atTop; refine ⟨hp.choices,hp.initialStage,hp.infinite.comp h,hp.uv.comp hφ,hp.physical.comp h,fun i=>hp.even _,fun i=>hp.atLeast _,fun i=>hp.normalized _,fun i=>hp.separate _,fun i=>hp.reference _,fun h=>hp.compare h,fun h=>hp.beta_min h,fun m=>?_,fun h=>hp.near h,?_⟩
    · obtain ⟨W,h⟩:= hp.size m; exact ⟨W,fun i hh=>h _ hh⟩
    exact ⟨hp.runs.1,fun η h=> (hp.runs.2 η h).mono fun i hi k hk=>hi _ hk⟩
omit hp
include hP
lemma roads : (res C P φ).System:=by
     refine ⟨?_, fun h=>hP.origin h,fun d=> ((hφ.tendsto_atTop).eventually (hP.mixing d)).mono fun i hh=>?_⟩
     · exact ⟨hP.sections.localizes,hP.sections.invariant,hP.sections.seed,hP.sections.unit,hP.sections.pin,hP.sections.charge,hP.sections.flavor,hP.sections.star,hP.sections.parity,hP.sections.mesons,hP.sections.baryons⟩
     exact ⟨hh.live, hh.unit,hh.pin,hh.charge,hh.flavor,hh.star,hh.parity,hh.calibration⟩
omit hP hφ
variable (T:Pollens P K)(F:Foil P K T)(H:K.Harmony P φ)
variable (A: EuPin →* (K.W≃ₗ[ℂ] K.W)) (L: Ortho.Skew→ K.W→ₗ[ℂ] K.W)
noncomputable abbrev equip:Fields:=⟨K.W,K.level,K.focus,lampU P K,T.adj,T.parity,T.charge,T.flavor,A,K.arc,L⟩
noncomputable local instance (K:Choir): NormedSpace ℝ K.W:=NormedSpace.restrictScalars ℝ ℂ _
local notation "E"=> equip T A L
include H F
variable (ha:∀ (p:EuPin) s,p.Lifts s → A p=T.spin p)
include ha
lemma turners (hB:∀ x:K.W,Continuous fun p=> A p x)(hx:∀ d x (h:x∈K.level d) p,A p x∈K.level d)(hF:∀ p u,Function.Commute ⇑(A p) ⇑(T.flavor u))(hA:∀ (X:Ortho.Skew) (x:K.W)p,EuPin.Path X p→HasDerivAt (fun y=> A (p y) x) (L X x) 0) : (equip T A L).System (res C P φ):=by
    refine ⟨fun d r=> H.h.tops ..,fun d=> inferInstanceAs (FiniteDimensional ℂ (K.level d)), H.h.slope,H.h.absorbs, F.unit, fun d u z a=>T.a ..,fun d r x p s h=>?_,fun d r x=>T.c ..,fun d r x u=>T.f ..,fun d r x=>T.p .., fun a=>T.reflex H.h a,T.even H.h,T.realL H.h,T.cadence H.h,fun u a=>T.activeF H.h a u, hB,fun x h p=>hx _ _ h _,fun p h hv=>?_,hF,hA,fun a d=> H.h.graded a d⟩ -- typ
    · change A p _= _; rw [ha p s h]; exact T.w p s h d r x
    change A p=T.parity; rw [ha p 1 (h.trans (map_one Signed.inclusionO).symm)]; exact T.signs H.h _ h hv
omit ha
variable (hh:∀ (p:EuPin) n (x:Points n)(hx:x∈conf n) u,K.total n (Points.move p.coord x) (A p ∘u)=K.total n x u)
include hh
lemma european : Fields.Euclidean (F:=equip T A L) K.total:=by
    refine ⟨fun n x hx z v=> F.translation n x hx z v,fun n x hx p _ u=> hh p n x hx u, fun a l h=> F.starry _ h a, F.parity,fun l r x y H' p q ht hv=> F.flips l r x y p q H' (?_) (?_),F.empty,fun n x hx=>F.functor _ _ hx, fun n u=> H.h.smooth _ _,fun n t j=>H.h.thick _ t j,fun n t p x hx a=>H.h.derivatives n x hx t p a,fun a n v he=> F.priests a n v he,fun a=>⟨F.vigor a⟩,fun v h=>F.realPair timeAxis v h⟩
    · unfold Fields.homogeneous at ht; cases p <;> exact ht
    unfold Fields.homogeneous at hv; cases q <;> exact hv
include hφ hp
lemma scaling : Fields.Scaling (F:=equip T A L) K.total (rod C φ) (res C P φ):=by
    have hk (p:Strip K) (h:Strip.distinct p)(t:E4 → E4)(u:K.W→ K.W)(H:∀ (n:ℕ)(x:Points n)(hx:x∈conf n)v, K.total n (points fun i=> t (x i)) (u ∘ v)= K.total n x v): Strip.tone (p.map fun i=> (t i.1,u i.2))=Strip.tone p:=by rw [show Strip.tone _= _ from (introduces (Q:=K) (fun x:E4 ×K.W=> t x.1) (fun x=>u x.2) p)]; exact H p.length (Strip.locus p) h _
    refine ⟨fun u p h=> hk _ h id (T.flavor u) (fun n x hx v=> F.flavor n x hx u v),fun s p h=> hk _ h (Ortho.move s.coord) (A s) (fun n x hx v=> hh s n x hx v),fun p h=>hk p h id T.charge (F.charge),?_,fun n d u v t hK hv ε he=>H.allS d v u t hK hv ε he⟩
    intro n x; exact visions hp hφ.tendsto_atTop x
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.scaling
#print axioms YM.Massive.Tarn.european
