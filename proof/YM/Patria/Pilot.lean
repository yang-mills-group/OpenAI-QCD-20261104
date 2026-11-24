import YM.Patria.Calm
/-! Endpoint harvest on common Borrows.We never fund a fixed cost hypothesized outside.Wagers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
variable {V:Hol su}(X:Lining.Temper.Collage.Exhibit V)(H:SourceRead.TaperHol)(C: Sequence)(base:ℕ→ℕ)(sym:RawSym)
open Lining Lining.Ferry Lining.Temper Lining.Temper.Collage
variable (M:Exhibit.CoreMix)
local notation "cal"=>X.display C H sym M base
noncomputable def Bloom (d:ℕ) : Bore d:= fun c b=> (Realize.placed (X.t d) c b).comp (X.lead d)
local notation "Γ"=> Bloom X
variable (hP:(X.display C H sym M base).SectionLaws)
include C H M base
lemma stays (d:ℕ) : Rubric sym (Γ d):=by
    have h:= X.ready C H sym M base; exact ⟨h.unit d,fun c x b p=> Canvas.stylus p _ b _ (c:=c),fun c x b=>h.parity d c b x,fun c x b u=>h.flavor _ _ _ _ u,fun c x b=>h.charge _ _ _ _,fun c x b s p hp=> h.pin _ _ _ _ p s hp,fun c x b a=>h.star _ _ _ _ a⟩
lemma carries (i d:ℕ)(ht: (C.A i).Actual) (h: OrderMix (C.A i) H sym (Γ d) (i:=base d) (fun v=>M d v i)): (X.display C H sym M base).Mixing d i:= by
    let T:=C.A i; refine ⟨h.active,fun v=>h.unitO v,fun v x p s hp=>h.pinO v x p s hp,fun v=> LinearEquiv.ext (fun x=>h.chargeO v x),fun v u=>LinearEquiv.ext (fun x=> h.flavorO v x u),fun v a x=> h.eyeO v x a,fun v=>LinearEquiv.ext (fun x=> h.parityO v x),fun x u=>?_⟩
    let Z:= draft C.S (C.R i) (Γ d) (C.N i) (base d) u ((M d u i) x); let G:= (C.A i).regulator.density* Z; refine ⟨fun m=>AllAt T m G,?_,holding T G (base d),stamps (h.smoke x u)⟩
    change ⇑(AllAt T (C.N i) G)= _; rw [origin,LinearMap.id_apply,ht.start]; unfold G; change ⇑(C.A i).regulator.density * ⇑Z = _ -- change notation
    have hz: Z= (X.display C H sym M base).marker x u i:=by unfold Z draft visitor; rw [smul_zero]; rfl
    rw [hz]
omit M
include sym
lemma upland (ht:∀ i,(C.A i).Actual)(hp:∀ i:ℕ,i≤8→base i=0)(hV:∀ d,∀ᶠ i in atTop,∃ W:Market C.S (C.R i) d, Wager (C.A i) H (Bloom X d) W (base d)) : ∃ M:Exhibit.CoreMix, (X.display C H sym M base).System:=by
    have hg : ∀ d i:ℕ, ∃ Q:PatchMix d, (∃ W:Market C.S (C.R i) d,Wager (C.A i) H (Bloom X d) W (base d))→ OrderMix (C.A i) H sym (Γ d) (i:=base d) Q:=by
       intro d i; by_cases he:∃ W: Market C.S (C.R i) d, Wager (C.A i) H (Bloom X d) W (base d)
       · obtain ⟨W,hW⟩:=he; obtain ⟨F,hF⟩:= hymn (C.A i) H sym (Γ d) (stays X H C base sym (fun _ _ _=>LinearEquiv.refl ..) d) (ht i) W hW; exact ⟨F,fun _=>hF⟩
       exact ⟨fun _=>LinearEquiv.refl ..,fun h=> False.elim (he h)⟩
    choose Q h using hg; let F: Exhibit.CoreMix:= fun d v i=> Q d i v; exact ⟨F,X.ready _ _ _ _ _,fun {i} hi=>hp _ hi,fun d=> (hV d).mono fun i hi=> carries X H C base sym F i d (ht i) (h d i hi)⟩
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.upland
