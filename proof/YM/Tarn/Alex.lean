import YM.Tarn.Phonic
/-! Orientation axioms in compact-friendly finite rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set
open scoped Topology BigOperators Classical Matrix
variable {C:Sequence} {P:Calibration C} (hQ:P.System) {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q:Choir} {φ:ℕ→ℕ}(H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)
namespace Choir.Harmony
open Domestic
include H hφ hp hQ
lemma images (a:Axis):∃ p:Q.W ≃ₛₗ[starRingEnd ℂ] Q.W,∀ u d z,p (Q.focus u d z)=Q.focus u d (P.sym.adj d a z):=by
    let t : Equiv.Perm (Fin 2):= Fin.revPerm; let W:= Signed.reflect a; have he:= H.h.counterparts (fun d=>P.sym.adj d a) (fun i=> (P.sym.adj i a).surjective) id t (fun x=>points fun i: Fin 2=> Ortho.move W (x (t i))) (affined W t) star (fun x hx v=>by
        exact adjustF hQ hp H hφ (fun i=> (v i).1) (fun i=>(v i).2.1) (fun i=>(v i).2.2) x hx a)
    obtain ⟨F,hF⟩:= H.h.crown (fun i=> (P.sym.adj i a).toLinearMap) id (fun i j u w p q hh=> he ⟨i,p,u⟩ ⟨j,q,w⟩ hh)
    have hV:Involutive F:=by intro x; obtain ⟨d,p,hp⟩:=H.h.tidal x none; rw [←hp,hF,hF]; have hv:P.sym.adj d a (P.sym.adj d a p)=p:= Subtype.ext (by rw [RawSym.adjActs,RawSym.adjActs]; exact UV.eyeTwist a p.val); exact congr_arg (Q.focus none d) hv
    exact ⟨LinearEquiv.ofBijective F hV.bijective,hF⟩
end Choir.Harmony
-- We keep returns for every signed lift. Supply laws.Missing continuous proper until torque.
structure Pollens (P:Calibration C)(Q: Choir) where
   parity: Q.W≃ₗ[ℂ] Q.W
   charge: Q.W≃ₗ[ℂ] Q.W
   flavor:FlavorTorus →* (Q.W≃ₗ[ℂ] Q.W)
   adj(a:Axis):Q.W≃ₛₗ[starRingEnd ℂ]Q.W
   spin(p:EuPin):Q.W≃ₗ[ℂ] Q.W
   c d u z: charge (Q.focus u d z)=Q.focus u d (P.sym.charge d z)
   p d u z: parity (Q.focus u d z)=Q.focus u d (P.sym.parity d z)
   f k d u z: flavor k (Q.focus u d z)=Q.focus u d (P.sym.flavor d k z)
   w p s (ht:p.Lifts s) d u z: spin p (Q.focus u d z)=Q.focus (Averaging.permute s u) d (P.sym.pin d p z)
   a k d u z: adj k (Q.focus u d z)=Q.focus u d (P.sym.adj d k z)
lemma signsFaith : Injective Signed.inclusionO:=by
    intro x y hx; have hh(i): x.matrix (y.perm i) i=y.matrix _ i:=congr_fun (congr_fun (congr_arg Subtype.val hx) _) i; have hp(i):x.perm i=y.perm i:=by by_contra h; have he:=hh i; simp [Signed.matrix_at,h] at he; split at he <;> norm_num at he
    refine Signed.ext (Equiv.ext hp) (funext fun i=>?_); have he:=hh i; simp [Signed.matrix_at,hp] at he; cases h:x.flip i <;> cases hv:y.flip i <;> first| rfl| norm_num [h,hv] at he
include H hp hφ hQ
lemma owned : Nonempty (Pollens P Q):=by
     choose A hA using fun a=> H.images hQ hp hφ a; obtain ⟨p,hp'⟩:= H.parityX hQ hp hφ; obtain ⟨q,hq⟩:= H.chargeX hQ hp hφ; choose f hf using fun v=> H.flavorX hQ hp hφ v
     have hz(p:EuPin):∃ F:Q.W≃ₗ[ℂ] Q.W, ∀ s:Signed,p.Lifts s →∀ u d z,F (Q.focus u d z)=Q.focus (Averaging.permute s u) d (P.sym.pin d p z):=by
          by_cases h:∃ s,p.Lifts s
          · obtain ⟨s,he⟩:=h; obtain ⟨t,h⟩:= H.shimmers hQ hp hφ p s he; refine ⟨t,fun x hv=>?_⟩; rw[show x=s from ?_]; exact h
            exact signsFaith (hv.symm.trans he) -- verify
          exact ⟨LinearEquiv.refl ..,fun s hv=> False.elim (h ⟨_,hv⟩)⟩
     choose Z hZ using hz; let M:FlavorTorus →* (Q.W≃ₗ[ℂ] Q.W):= {
            toFun:=f
            map_one':=by
               ext1 x; obtain ⟨d,p,rfl⟩:= H.h.tidal x none -- ob? x occ.
               rw [hf]; have h:P.sym.flavor d 1 p=p:= Subtype.ext (by rw [RawSym.flavorActs]; exact UV.flavor_unit _); rw [h]; rfl
            map_mul' :=fun u v=>by
               ext1 x; obtain ⟨d,p,rfl⟩:= H.h.tidal x none; change f (u*v) _=f u ((f v) _); rw [hf,hf,hf]; refine congr_arg _ (Subtype.ext ?_); rw [RawSym.flavorActs, RawSym.flavorActs,RawSym.flavorActs]; exact (flavor_coil ..).symm }
     exact ⟨⟨p,q,M,A,Z,(fun d u=>hq u d),(fun d u=>hp' u d),(fun k d u=>hf k u d),(fun p s h d u=>hZ p s h u d),(fun k d u=> hA k u d)⟩⟩
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.owned
