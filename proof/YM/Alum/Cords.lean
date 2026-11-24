import YM.Alum.Wreath
import YM.Alum.Arbor
/-!
# Select a dual margin at a common canonical center. both orth arrays from registered glyphs. source Font Type B.S
-/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Tarot
open Pilgrim Column Goblet
variable {c n m:Side}(g: Ratio c n)(r:Ratio m n)(P:Site c)(hp:Even c.val)(he:Even m.val)(hk:Odd g.count.val)(hr:Odd r.count.val)
variable {I:Type}[Fintype I](x:I → Site n)(t:Site n)(X Y U:ℕ)
variable (h:∀ i,separation (x i) t ≤ X) (ht:X+r.count.val + U ≤ g.count.val/2) (hv:0 <Y)
include h ht hv hr he hp hk
lemma wells (hf: (Fintype.card I+1)*(2*Y)<r.count.val)(hG:∀ i j,i≠j→ r.count.val <separation (x i) (x j)) : ∃ z:Site n,∃ P:I→ Site m, Injective P ∧∀ i, x i∈(mural g hp z).margin 0 U ∧ x i∈(mural r he z).margin (P i) Y:=by
     let v := Sum.elim x (fun _ : Unit=>t); obtain ⟨w,hw⟩:= Vent.balm r he v Y hv (by simpa using hf); choose p hP using hw; let i0:=p (.inr ()); let B(i:I):=p (.inl i)-i0; let z:=w+r.embed i0
     refine ⟨z,B,?_,fun i=>?_⟩
     · intro i j h; by_contra ht; have he': p (.inl i)=p (.inl j):= sub_left_inj.mp h; apply not_le_of_gt (hG i j ht); exact ((mural r he w).extent (show x i∈_ from (hP (Sum.inl i)).1) (he'.symm ▸ (show x j ∈ (mural r he w).chamber (p (Sum.inl j)) from (hP _).1))) -- binder proof
     have hpV : x i∈ (mural r he z).margin (B i) Y:= (Goblet.margV r he w i0 (B i) hr _ _).1 (show x i∈ (mural r he w).margin (i0+B i : Site m) Y from (by rw [show i0+B i=p (Sum.inl i) from (by unfold B; abel)]; exact hP (.inl i))) -- add_sub_cancel order.Edit
     refine ⟨(key_margin g z _ 0 hp hk _).2 ?_, hpV⟩; rw (transparency:=.default) [show g.embed 0=0 from g.root.map_zero,add_zero];
     have hx: separation t z+Y ≤r.count.val/2:= (key_margin r _ _ _ he hr _).1 (hP (.inr ())); have hu:=separation_triangle (x i) t z; specialize h i; omega
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.wells
