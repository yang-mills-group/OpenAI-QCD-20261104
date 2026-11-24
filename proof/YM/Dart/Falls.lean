import YM.Dart.Bier
import YM.Dart.Book
/-!
  Slot expansion identities. Coefficient-scaled.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}
local notation "S"=> C.S
set_option quotPrecheck false
local notation "L" i:arg=> C.S.side (C.R i) (C.N i)
open Elm.SparK.Arbor Elm.SparK.Arbor.PlaneG
variable (W:Pins d) {H:Source.Hol su}(A:Lining.Temper.Collage.Exhibit H) (C:Sequence) (Θ: Massive.SourceRead.TaperHol) (sym:RawSym)(PV:Lining.Temper.Collage.Exhibit.CoreMix)(base:ℕ→ℕ)
local notation "P₀"=> A.display C Θ sym PV base
-- height composition
variable (u:UV.Label d)(p:Cover)
local notation "ζ" i:arg=> (stem P₀ d i u)
local notation "α" k:arg i:arg=> ((W.basic.coord k) (PV d none i u))
lemma tier : (fun i=>shifting C i p (stem P₀ d i u)) = ∑ k:Raw d,(fun i:ℕ=> ((W.basic.coord k) (PV d none i u)) • (hymn A (W.f k).mark p) (C.S.side (C.R i) (C.N i))) :=by
    ext1 i; let f:Label d→ₗ[ℂ] stalk C i:=LinearMap.pi (fun b:Cover=> (Depth.Bloom A d (C.S.side (C.R i) (C.N i)) (b+p)))
    have he : shifting C i p (stem P₀ d i u)= f (PV d none i u):=rfl
    have h : f (PV d none i u) = ∑ k:Raw d,α k i • f ((W.f k).mark) := by
         simp_rw[← W.idV,← map_smul,← map_sum]; rw [show ∑ k:Raw d,α k i • W.basic k= PV d none i u from W.basic.sum_repr _]
    rw [he,h,Finset.sum_apply]; apply Finset.sum_congr rfl; intro k _; apply congr_arg (α k i • ·); ext1 b; change Bloom A d (C.S.side (C.R i) (C.N i)) (b+p) (W.f k).mark= Bloom A d (C.S.side (C.R i) (C.N i)) (p+b) (W.f k).mark; rw[add_comm b p]
end YM.Massive.Needle
#print axioms YM.Massive.Needle.tier
