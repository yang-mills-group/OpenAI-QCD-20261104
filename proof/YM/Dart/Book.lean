import YM.Dart.Pants
/- Before purchasing, frame of all finite labels. Support leases per-symbol 
   even for translated insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans Poised.Stative MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
namespace PlaneG
open Gallery Intag.Vale Arise.Range
-- all base crew in homogeneous spin layer
abbrev Raw (d:ℕ) := Fin (Module.finrank ℂ (Label d))
structure Pins (d:ℕ) where
   f: Raw d→Text d
   basic: Module.Basis (Raw d) ℂ (Label d)
   idV:∀ i,basic i= (f i).mark
lemma ripe(d:ℕ):Nonempty (Pins d):=by
    let f:=fun i:Text d=>i.mark; let S:=Set.range f; have h:Submodule.span ℂ S= ⊤:=by
         refine eq_top_iff.mpr fun w _=>?_ ; rw [←sumCut w]; refine Submodule.sum_mem _ fun i _=>Submodule.subset_span ?_; exact ⟨⟨_,i, Massive.Evo.canCut i.val w.val⟩,rfl⟩
    obtain ⟨X,hX,hP,hM⟩:=Intag.Vale.draws (V:=Label d) S h; choose F hF using hX; let Q:=Module.Basis.mk hM hP.ge; exact ⟨F,Q,fun i=> (Module.Basis.mk_apply hM hP.ge i).trans (hF i).symm⟩
variable (C:Sequence) {H:YM.Source.Hol su}(θ:SourceRead.TaperHol)(A:Lining.Temper.Collage.Exhibit H) (M: Lining.Temper.Collage.Exhibit.CoreMix) (base:ℕ→ℕ)(sym:RawSym)
noncomputable abbrev hymn (x:Label d)(b:Cover):Drape:=fling b (grant (A.t d) (A.lead d x))
lemma beam_cost (x:Text d) (b:Cover): Draft (hymn A x.mark b) 0 x.era.val.2.2:=by
     refine hooking (A.t d) _ _ _ fun V=>?_ ; rw [A.label]; let L:= layer (Pairs (Cylinder.Nearest (A.t d) 6)) x.era.val.2.2
     have hp:=x.stamp
     refine Submodule.span_induction (p:=fun y _=>glaze (A.F d) (A.U d) (A.t d) V y ∈ L) ?_ (by rw [map_zero]; exact L.zero_mem) (fun a b _ _ h hp=>by rw [map_add]; exact L.add_mem h hp) (fun i a _ h=> by rw [map_smul]; exact L.smul_mem _ h) hp
     rintro y ⟨i,hi,rfl⟩; have hh:i.2.card= x.era.val.2.2:=hi.2.2; unfold L; rw [←hh]; exact Carte.Cells.porch_part H A i V
local notation "P"=>A.display C θ sym M base
include C θ M base
lemma mirrors (x:Text d)(b:Cover)(a:Axis): via a (hymn A x.mark b)= hymn A (opposite sym a x).mark (axisT a b):=by
     let u:= x.mark; have h:= A.ready C θ sym M base; funext n v; apply ContinuousMap.ext; intro U
     let p:= P; have hv:= h.star d n (b+axisT a v) x.mark a; have hX: (Signed.mirror a).act (b+axisT a v) = axisT a b+ v:=by rw [Signed.act_add]; exact congr_arg (axisT a b+·) (axis_sq a v)
     rw[hX] at hv; exact congr_fun hv U
variable (x:Text d)
structure Asset (X:Drape)(s:ℕ):Prop where
    shape: Profile X
    bore : ∀ l:List Axis,Draft (evoc X l) 0 s
include sym M base
lemma veins (b:Cover): Asset (hymn A x.mark b) x.era.val.2.2:=by
     let u:= x.mark; let V:=hymn A u b; have h:= A.ready C θ sym M base
     refine ⟨fun n o=>h.invariant d n (b+o) u,fun L=>?_⟩
     have h(l:List Axis):∃ w:Text d,∃ o:Cover,w.era=x.era ∧ evoc V l= hymn A w.mark o:=by
          induction l with
          | nil=>exact ⟨x,b,rfl,rfl⟩
          | cons a l ih=> obtain ⟨w,x,h,hx⟩:=ih; exact ⟨opposite sym a w,axisT a x,h,by rw[evoc,hx]; exact mirrors C θ A M base sym ..⟩
     obtain ⟨w,o,h,hx⟩:=h L; rw [hx,←h]; exact beam_cost A w o
end PlaneG
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.veins
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.ripe
