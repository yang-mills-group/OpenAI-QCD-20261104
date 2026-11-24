import YM.Alum.Zinc
/-!
  Interval selection: cuts divide early/late for strict stencil roots
  on native integer lifts. Layout persists while any set of small sweeps.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet
variable {n c l d:Side}
open Chess Cells Romance Massive.Lyre.Array Plum Patria
variable (T:Tiling n)(a:Axis)(x y:Cover)(u v:T.Cell)
local notation "P₀"=> T.bandCut v a
local notation "Δ"=> (step a : Cover)
local notation "B"=>T.chamber u
variable (hv:T.kind=.link)
-- late must fit travel with price. projection bound.Coherent through.Clock.
include hv
lemma cutP (hx:wrap _ x∈T.chamber u)(hy:wrap _ y∈T.chamber v)(ht:(T.side.val:ℤ)≤ y a-x a)(hh:y a-x a ≤ ((↑n.val:ℤ))/2): u∈ T.minusCells v a ∧ v∈ T.plusCells v a:=by
      let V:= T.bandCut v a; let z:= T.starts v a; let k:= T.coordinated v (wrap _ y) a; have hK:k<T.side.val:= T.small hy a
      have Hk:z+(k:Per n)= (y a:Per n):= T.indent ..
      have he : wrap n x ∉ V.sector:=by
          intro h; let s:= V.distance (wrap n x); have hs:s<V.half.val:= (show s<V.half.val from by
                  have hh: V.kind.Strict V.half.val s:= h; rw[show V.kind=.link from hv] at hh; exact hh)
          have hp:z+(s:Per n)= (x a:Per n):=by
             have ht:= V.back (wrap n x); change (s:Per n)=(x a:Per n)-z at ht; rw [ht]; abel
          let X:= y a-(x a)-k; have hX:0<X:=by unfold X; omega
          have ht:X ≤ V.half.val:=by have h:=V.even; unfold X; omega
          have he:X.toNat + s>0:=by omega
          have hx : X.toNat+s<n.val:=by have h:=V.even; omega
          have hy:((X.toNat+s:ℕ):Per n)=0:=by rw [Nat.cast_add,← Int.cast_natCast (X.toNat), Int.toNat_of_nonneg hX.le,show X=y a-x a-k from rfl,Int.cast_sub,Int.cast_sub,Int.cast_natCast,← Hk,←hp]; abel
          apply Nat.ne_of_gt he; rw [←ZMod.val_natCast_of_lt hx, hy, ZMod.val_zero]
      refine ⟨(T.negative ..).2 (fun h=> he (T.within v a _ ((T.positive_side ..).1 h) hx)),(T.positive_side ..).2 (by simpa using T.widthHalf.pos)⟩
-- distance in integer units
omit hv
lemma costsD{b i:ℕ}(h:i ≤ 4*b) : ∀ j:Axis, ((depthShift a b i) j).natAbs < 4*b+1:=by
    intro j; unfold depthShift; by_cases e:j=a; · subst j; simp; omega
    simp [e]; -- step_neg
lemma shifted {x z:Cover}(v:T.Cell){k b:ℕ}(hx:wrap n x ∈ T.margin v (k+b))(h:∀ i:Axis,(z i).natAbs< k): wrap n (x+z) ∈ T.margin v b:=by rw [add_comm,map_add]; exact marginB T hx h
variable (b K k:ℕ) (hx:wrap n x∈ T.margin u (4*b+1+k)) (hy: wrap n y∈ T.margin v (4*b+1+k))
variable (X Y:Cover→ Stud n 6)
structure FlowsP (R: Regulator n 6)(v:T.Cell)(k:ℕ)(X:Cover→Stud n 6)(W:ℝ) : Prop where
    along (G H:Cover): Patria.march H (X G)= X (G+H)
    printC y : wrap n y ∈ T.margin v k → Fence (T.chamber v) (X y)∧Potion (X y)∧topH T R (X y) v ≤ W
variable (R:Regulator n 6)(hK:Smoke T R)(hs:0<R.Z)(W:ℝ)(ho:0 ≤ W)
variable (hX:FlowsP T R u k X W)(hY:FlowsP T R v k Y W)
include hx hy hK hs hX hY ho
lemma pairFlow (hv:u∈ T.minusCells v a)(hw:v ∈ T.plusCells v a) (hb:0<b)(d:ℕ)(hd:d ≤ b) : ‖valueH R (X x * Y (y+(2*d) • step a)) - valueH R (X x * Y y)‖ ≤ d*(4*W^2/(b:ℝ)) :=by
       rw [← hY.along]; apply anchored T R (X x) (Y y) v u v a hK hs b d W ho hb hd hv hw; · intro i hi; rw [hX.along]; exact hX.printC _ (shifted T u hx (z:= -(depthShift a b i)) fun j=> (by simpa only [Pi.neg_apply, Int.natAbs_neg] using (costsD a hi j)))
       intro i hi; rw[hY.along]; exact hY.printC _ (shifted T v hy (costsD a hi))
end Goblet
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.pairFlow
#print axioms YM.Massive.Lyre.Goblet.cutP
