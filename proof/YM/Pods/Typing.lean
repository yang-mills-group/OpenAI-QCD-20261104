import YM.Pods.Cove
import YM.Pods.Rooms
/-! Point-source primitive observation budgets on regulator, ALL lift orientations.
Carry alongside long histories. Uses fix ε before actual data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Hub
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry
variable {c f m:Side}(S:Scheme) (b:Side){n k d:ℕ}{F:ℕ}
lemma evenW (hb:Even b.val)(i:ℕ): Even (S.side b i).val:=by rw [Scheme.side,PNat.mul_coe]; exact hb.mul_right _
abbrev viewW (h:k≤n) : Ratio (S.side b k) (S.side b n):=⟨⟨ratioTo S n k,(odd_to h).pos⟩, by simp_rw [Scheme.side, PNat.mul_coe]; rw [factorize (S:=S) h]; exact (mul_assoc ..).symm⟩
lemma viewOdd (h:k≤n): Odd (viewW S b h).count.val:=odd_to h
-- proof in Itinerary casts.F.Body.Co.Trans mother.Perch.G any side.Tick roll.
lemma ratioUnique {c f:Side}(u v:Ratio c f): u=v :=by rcases u with ⟨j,h⟩; rcases v with ⟨i,hp⟩; have he:j=i:=PNat.eq (Nat.eq_of_mul_eq_mul_left c.property (h.symm.trans hp)); subst i; rfl
-- Allow replacing period! side proof P lattice.In cast.For dimensions def.
lemma shiftChart (e:c=m)(u:Ratio c f)(v:Ratio m f)(he:Even c.val)(hg:Even m.val)(w:Site f): mural u he w=mural v hg w:=by subst m; rw [ratioUnique u v]
lemma markChart (e:c=m)(u:Ratio c f)(v:Ratio m f)(he:Even c.val)(hg:Even m.val)(w:Cover)(Z:Regulator f 6)(x:Insertion f 6) : floorL (mural u he (wrap f w)) Z.average Z x 0=floorL (mural v hg (wrap f w)) Z.average Z x 0:=by subst m; rw [ratioUnique u v]
-- f.P centred view. loop selecting post. factor exponential via Pt clocks. Includes Marquee occupancy not just density. extract.
variable {d:ℕ} {C:Sequence} (P:Calibration C)
local notation "root" => C.S
local notation "Stk" p:arg => C.A p
local notation "gq" i:arg => C.S.side (C.R i)
set_option quotPrecheck false
-- height bounds per nonzero moored.Homogeneous. later split use both prior P.System. add support Pin boundary.
structure PointTariff (u:Label d)(q:Bool) : Prop where
   envelope {ε:ℝ}: moored u.val q→ u≠0 →0<ε →∃ c:ℝ,0 ≤ c∧∀ᶠ j in atTop,∀ᶠ i in atTop,∀ (h:j ≤ C.N i) (he:Even (C.S.side (C.R i) j).val) (x:Cover), let g:= viewW C.S (C.R i) h; let T:= mural g he (wrap _ x); let R:= (C.A i).regulator; floorL T R.average R (P.physical (d:=d) none i u x) 0≤ c * Real.exp (((d:ℝ)/2+ε)* Real.log ((C.S.spacing j)⁻¹))
-- use prefix without ∀ᶠ j? yes.
abbrev Spent(C:Sequence)(P:Calibration C):= ∀ (d:ℕ) (u:Label d)(q:Bool), PointTariff P u q
lemma cloth (f:List Axis→ℝ)(h:ℕ):∃ c:ℝ,0≤ c∧∀ l:List Axis,l.length≤h→ f l≤c:=by
    induction h generalizing f with
    | zero=> exact ⟨max 0 (f []),le_max_left ..,fun i hi=> by have h:i=[]:=List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hi); rw [h]; exact le_max_right ..⟩
    |succ h ih=>
       choose C hc hv using fun i:Axis=> ih (fun l=> f (i::l)); refine ⟨max (∑ i:Axis,C i) (f []), (Finset.sum_nonneg (fun i _=> hc i)).trans (le_max_left ..),?_⟩; intro i hi; rcases i with _|⟨x,l⟩; exact le_max_right ..; exact (hv x l (Nat.le_of_succ_le_succ hi)).trans ((Finset.single_le_sum (fun i _=> hc i) (Finset.mem_univ x)).trans (le_max_left ..))
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.markChart
