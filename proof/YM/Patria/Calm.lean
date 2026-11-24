import YM.Patria.Orchid
/-! Exact common mixing consumer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
variable {S:Scheme}{r:Side}{N d i:ℕ}
variable (A:Run S N r 6)(H:SourceRead.TaperHol)(sym:RawSym)(B:Bore d)
variable (hf:Rubric sym B)(u:Averaging)(hA:A.Actual)(W:Market S r d)(hW:Wager A H B W i)
open Poised Plans Display Orientation Exposure Rolls Canvas
local notation "Φ"=>Fuel A H B i
variable (X Y: Label d)(uv: FlavorTorus)(s:Signed)(p:EuPin)(a:Axis)
abbrev PatchMix (d:ℕ):= Averaging→ (Label d≃ₗ[ℂ] Label d)
structure OrderMix (Q: PatchMix d) : Prop where
    active: i ≤ N
    unitO u: Q u (sym.unit d)=sym.unit d
    pinO u x p s (h: EuPin.Lifts p s): sym.pin d p (Q u x)= Q (Averaging.permute s u) (sym.pin d p x)
    chargeO u x : sym.charge d (Q u x)= Q u (sym.charge d x)
    parityO u x : sym.parity d (Q u x)= Q u (sym.parity d x)
    flavorO u x v: sym.flavor d v (Q u x)= Q u (sym.flavor d v x)
    eyeO u x a: sym.adj d a (Q u x)=Q u (sym.adj d a x)
    smoke x u: Fuel A H B i u (Q u x) x
include hf hW hA
lemma fit : ∃ f: Label d ≃ₗ[ℂ]Label d,∀ x,Φ u x (f x):=by
    choose Y h using fun x=> concordance A H sym B hf u hA x W hW
    let Z: Label d→ₗ[ℂ]Label d:={toFun:= Y,map_add':=fun x y=> Canvas.consensus _ _ _ (h _) _ (fuel_plus A H B u _ _ _ _ (h x) (h y)), map_smul':=fun c x=> Canvas.consensus _ _ _ (h _) _ (fuel_by A H B u _ _ c (h x))}
    have hx(x): Z (sym.parity d x)=sym.parity d (Z x):= Canvas.consensus _ _ _ (h _) _ (grading A H sym B hf u hA W hW x (Z x) (h x))
    have hh(x):Z x=0 →x=0:=by
         intro he; have hp(u0:Bool)(g :Label d)(ht:moored g.val u0)(hh:Z g=0):g=0:=by
             by_contra hv; obtain ⟨y,hv,hg⟩:= arises_nonzero A H B u hA g W hW u0 hv ht; apply hv; rw [← hh]; exact Canvas.consensus _ _ _ hg _ (h g)
        -- test
         have hh (q:Bool):facing sym q x=0:=by
             apply hp q _ (fronting sym x q); unfold facing; rw [map_smul]; split
             · rw [map_sub Z, hx,he,map_zero,show (0:Label d)-(0:Label d)=0 from sub_self (0:Label d),smul_zero]
             rw [map_add,hx,he,map_zero,add_zero,smul_zero]
         exact (revelation sym x).trans (by rw [hh, hh,add_zero])
    have hu:Injective Z:= fun x y he=> sub_eq_zero.mp (hh _ (by rw [map_sub Z,he,sub_self]))
    have hs:Function.Surjective Z:=by have hf := (LinearMap.injective_iff_surjective (K:=ℂ) (V:=Label d) (f:=Z)).1 hu; exact hf
    exact ⟨LinearEquiv.ofBijective Z ⟨hu,hs⟩,h⟩
lemma hymn :∃ Q: PatchMix d, OrderMix A H sym B (i:=i) Q:=by
    choose f h using (fun u=> fit A H sym B hf u hA W hW); let U(v):=(f v).symm
    have he(x:Label d)(y:Label d)(v:Averaging)(he:Φ v y x): y=U v x:=by
        apply (f v).injective; unfold U; rw [LinearEquiv.apply_symm_apply]; exact Canvas.consensus _ _ _ (h v _) x he
    have hX(v:Averaging)(x): Φ v (U v x) x:= by have h:= h v ((f v).symm x); rwa [(f v).apply_symm_apply] at h
    refine ⟨U,hW.siteM,fun v=>(he _ _ _ (bequeath A H sym B hf v hA W hW)).symm,fun u x p s hp=>he _ _ _ ?_,fun u x=>he _ _ _ ?_,fun u x=>he _ _ _ ?_,fun u x v=>he _ _ _ ?_,fun u x a=>he _ _ _ ?_,fun x v=>hX v x⟩
    · exact merch A H sym B hf u hA W hW _ _ s p (hX u x) hp
    · exact debit A H sym B hf u hA W hW _ _ (hX u x)
    · exact grading A H sym B hf u hA W hW _ _ (hX u x)
    · exact rotary A H sym B hf u hA W hW _ _ v (hX u x)
    exact adjFlux A H sym B hf u hA W hW _ _ a (hX u x)
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.hymn
