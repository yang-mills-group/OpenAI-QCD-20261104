import YM.Tarn.Ambra
/-! Finite pre-Euclidean action -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set Domestic
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} (hQ:P.System) {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q:Choir} {φ:ℕ→ℕ}(H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)
lemma affined (s:Ortho)(ρ:Equiv.Perm (Fin n)):∀ x∈conf n,∃ y∈conf n,(points fun i:Fin n=>Ortho.move s (y (ρ i)))=x:=by
    intro x hx; refine ⟨Points.move s⁻¹ (Points.rearrange ρ.symm x),Points.move_in _ (Points.rearrange_in _ hx),?_⟩; ext1 i; simp
namespace Domestic
variable (h:Q.Domestic)
include h
private lemma rich {d:ℕ}(F:Q.W→ₗ[ℂ]Q.W)(s:Label d≃ₗ[ℂ]Label d)(u u':Averaging) (hx:∀ z: Label d,F (Q.focus u d z)= Q.focus u' d (s z)): BijOn F (Q.level d) (Q.level d):=by
    let V:=Q.level d; have he(x:Q.W)(u:Averaging): x∈Q.level d → ∃ p:Label d,Q.focus u d p=x:= fun hv=> (show x∈LinearMap.range (Q.focus u d) from h.tops u d|>.symm ▸ hv)
    have hW(v:Label d)(u:Averaging):Q.focus u d v∈Q.level d:= h.tops u d ▸ LinearMap.mem_range_self ..
    have hL(x:Q.W)(hy:x∈V):F x∈ V:= by obtain ⟨p,rfl⟩:=he x u hy; rw[hx]; exact hW _ _
    have hR:SurjOn F V V:=by intro v hv; obtain ⟨p,rfl⟩:= he _ u' hv; obtain ⟨x,rfl⟩:=s.surjective p; exact ⟨_,hW x u,hx _⟩
    let Y:V→ₗ[ℂ] V:= (F.comp V.subtype).codRestrict V (fun z=> hL z z.property);
    have hs:Surjective Y:=by rintro ⟨v,hv⟩; obtain ⟨x,hx,H⟩:= hR hv; exact ⟨⟨_,hx⟩,Subtype.ext H⟩
    refine ⟨fun x hx=> hL x hx,fun x hx y hy H=>?_ ,hR⟩; exact congr_arg Subtype.val ((LinearMap.injective_iff_surjective.mpr hs) (show Y ⟨x,hx⟩=Y ⟨y,hy⟩ from Subtype.ext H))
lemma fetched (F:Q.W→ₗ[ℂ]Q.W) (L:∀ d,Label d ≃ₗ[ℂ] Label d)(u u':Averaging) (hx:∀ d z,F (Q.focus u d z)=Q.focus u' d (L d z)): Bijective F:=by
    have hr(d):=rich h F (L d) u u' (hx d)
    constructor
    · intro x y hh; obtain ⟨d,hd⟩:=h.absorbs x; obtain ⟨p,hp⟩:= h.absorbs y; let m:=max d p; exact (hr m).2.1 (h.slope (le_max_left ..) hd) (h.slope (le_max_right ..) hp) hh
    intro y; obtain ⟨d,hd⟩:= h.absorbs y; obtain ⟨x,hp,hV⟩:=(hr d).surjOn hd; exact ⟨_,hV⟩
end Domestic
namespace Harmony
include H
private lemma rises (L:∀ d,Label d ≃ₗ[ℂ]Label d)(s:Ortho)(G:Averaging→ Averaging)(h:∀ t: Fin 2→Ticket,∀ x∈conf 2,Q.total 2 (Points.move s x) (moor Q∘ shiftT (fun d=> L d) G ∘ t)= Q.total 2 x (moor Q ∘t)) :∃ L':Q.W≃ₗ[ℂ]Q.W,∀ u d z,L' (Q.focus u d z)=Q.focus (G u) d (L d z):=by
     have he:= counterparts H.h (fun i=> L i) (fun i=>(L i).surjective) G 1 (Points.move s) (affined s (1:Equiv.Perm (Fin 2))) id (fun x hx v=>h v x hx)
     obtain ⟨F,hF⟩:= H.h.crown (fun i=>(L i).toLinearMap) G (fun i j u w p q hh=>he ⟨i,p,u⟩ ⟨j,q,w⟩ hh)
     exact ⟨LinearEquiv.ofBijective F (H.h.fetched F L none (G none) (hF none)),hF⟩
include hp hφ hQ
lemma shimmers (p:EuPin)(s:Signed)(h:p.Lifts s) :∃ t:Q.W≃ₗ[ℂ]Q.W,∀ u d z,t (Q.focus u d z)= Q.focus (Averaging.permute s u) d (P.sym.pin d p z) :=by
     refine rises H (fun d=>P.sym.pin d p) p.coord (Averaging.permute s) (fun v x hx=>?_); exact spinning hQ hp H hφ (fun i:Fin 2=>(v i).1) (fun i=> (v i).2.1) (fun i=>(v i).2.2) x hx s p h
lemma chargeX :∃ L:Q.W≃ₗ[ℂ] Q.W,∀ u d p,L (Q.focus u d p)=Q.focus u d (P.sym.charge d p):=by
    refine H.rises (fun d=> P.sym.charge d) 1 id (fun v x hx=>?_); rw [show Points.move 1 x=x from by ext1; simp]; exact chargeed hQ hp H hφ (fun i=>(v i).1) (fun i=>(v i).2.1) (fun i=>(v i).2.2) x hx
lemma flavorX (q:FlavorTorus) :∃ L:Q.W≃ₗ[ℂ] Q.W,∀ u d p,L (Q.focus u d p)=Q.focus u d (P.sym.flavor d q p):=by
    refine H.rises (fun d=> P.sym.flavor d q) 1 id (fun v x hx=>?_); rw [show Points.move 1 x=x from by ext1; simp]; exact flavored hQ hp H hφ (fun i=>(v i).1) (fun i=>(v i).2.1) (fun i=>(v i).2.2) x hx q
lemma parityX :∃ L:Q.W≃ₗ[ℂ] Q.W,∀ u d p,L (Q.focus u d p)=Q.focus u d (P.sym.parity d p):=by
    refine H.rises (fun d=> P.sym.parity d) 1 id (fun v x hx=>?_); rw [show Points.move 1 x=x from by ext1; simp]; exact parityed hQ hp H hφ (fun i=>(v i).1) (fun i=>(v i).2.1) (fun i=>(v i).2.2) x hx
end Harmony
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Harmony.shimmers
#print axioms YM.Massive.Tarn.Choir.Harmony.chargeX
#print axioms YM.Massive.Tarn.Choir.Harmony.flavorX
#print axioms YM.Massive.Tarn.Choir.Harmony.parityX
