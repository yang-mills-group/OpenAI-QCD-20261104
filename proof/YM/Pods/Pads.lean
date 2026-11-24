import YM.Patria.Pilot
/-! One-system consumer on ledger -- keep point and avg calibrations pinned.
Coordinates for each Run Tally at origin.
-/
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
local notation "Γ"=> Bloom X
lemma enclave (ht:∀ i,(C.A i).Actual) (hp:∀ i:ℕ,i ≤8→ base i=0)(hV:∀ d,∀ᶠ i in atTop,∃ W:Market C.S (C.R i) d, Wager (C.A i) H (Bloom X d) W (base d)) : ∃ M:Exhibit.CoreMix, (X.display C H sym M base).System ∧ ∀ (d i:ℕ) (W:Market C.S (C.R i) d), Wager (C.A i) H (Bloom X d) W (base d) → OrderMix (C.A i) H sym (Γ d) (i:=base d) (fun v=> M d v i):=by
    have hg : ∀ d i:ℕ, ∃ Q:PatchMix d, (∃ W:Market C.S (C.R i) d,Wager (C.A i) H (Bloom X d) W (base d))→ OrderMix (C.A i) H sym (Γ d) (i:=base d) Q:=by
       intro d i; by_cases he:∃ W: Market C.S (C.R i) d, Wager (C.A i) H (Bloom X d) W (base d)
       · obtain ⟨W,hW⟩:=he; obtain ⟨F,hF⟩:= hymn (C.A i) H sym (Γ d) (stays X H C base sym (fun _ _ _=>LinearEquiv.refl ..) d) (ht i) W hW; exact ⟨F,fun _=>hF⟩
       exact ⟨fun _=>LinearEquiv.refl ..,fun h=> False.elim (he h)⟩
    choose Q h using hg; let F: Exhibit.CoreMix:= fun d v i=> Q d i v; exact ⟨F,⟨X.ready _ _ _ _ _,fun {i} hi=>hp _ hi,fun d=> (hV d).mono fun i hi=> carries X H C base sym F i d (ht i) (h d i hi)⟩,fun d i W hw=> h d i ⟨W,hw⟩⟩
-- local footprint helpers
open Poised Plans
variable {d:ℕ} (x:Label d)(p: Bool) (a: Axis)(g:EuPin)
lemma moored_iff : moored x.val p ↔ sym.parity d x= ((if p then (-1:ℂ) else (1:ℂ)) • x):=by unfold moored; rw [← sym.parityActs,_root_.Subtype.ext_iff]; cases p <;> rfl
variable {S:Scheme}{N:ℕ}{r:Side}
variable {Q:PatchMix d} (B:Bore d) (A:Run S N r 6)
-- further.L. Pick.O orientation at cutoff
lemma mooredMix (b:ℕ) (h:OrderMix A H sym B (i:=b) Q) (hp:moored x.val p) (u:Averaging) : moored (Q u x).val p:= by
    apply (moored_iff sym _ p).2; rw [h.parityO u x,(moored_iff sym _ p).1 hp,map_smul]
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.enclave
#print axioms YM.Massive.Patria.Depth.mooredMix
