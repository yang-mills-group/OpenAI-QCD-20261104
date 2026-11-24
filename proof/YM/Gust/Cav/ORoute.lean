import YM.Next.ROTATIONS.Route
import YM.Gust.Cav.OYard
/- Variant of YM.Next.ROTATIONS.Route, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Function Filter Set MeasureTheory Measure Complex Row OS Ward Table Climb Analysis Work.A01
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {L : Register G} {S : Table L} {m : ℕ}
abbrev draught (x : Points (m+1)) (q : Fin (m+1)→ S.Tag) (J : Stress S) (a b l : Axis) (n : ℕ) (y : E4) :=
    ∑ d∈other a, breeze J q x a b l d n y
lemma drained (x : Points (m+1)) (hx : x∈conf _) (q : Fin (m+1)→ S.Tag) (J : Stress S) (P : DiffPlan S) (H : S.Hierarchy) (hp : P.Derivatives S) (hi : P.Orientation H.spin)
    (C : Conserved P H.spin J) (hr : RawTensor H.spin J) (a b l : Axis) (hh : a≠b) (ht : onLine l x) :
    (∀ᶠ n in atTop, Integrable (draught x q J a b l n)) ∧ Budget (-1) (fun n => ∫ y,draught x q J a b l n y) := by
  have he d (h : d∈other a) := blows a b l d (Finset.mem_erase.mp h).1 hh P hp H hi J hr C q x hx ht
  have hv : ∀ᶠ n in atTop, ∀ d∈other a, Integrable (breeze J q x a b l d n) := (eventually_all_finset _).mpr fun d hd => (he d hd).1
  refine ⟨hv.mono fun n h => integrable_finsetSum _ h,?_⟩
  exact (budget_sum (other a) (fun d n => integral volume (breeze J q x a b l d n)) _ (fun d h => (he d h).2)).same
    (hv.mono fun n hn => (integral_finsetSum _ hn).symm)
end YM.Spiral.Outer

#print axioms YM.Spiral.Outer.drained
