import YM.Ward.Genuine
import YM.Gust.Cav.Sum
/- Variant of YM.Ward.Genuine, for Spiral register. -/

/-!
# Singleton-singleton row. `arc` coordinate sign d(t,j)=Ω x.
Pair responder and analytic positive radial kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spiral.Ward
open Function Set Filter Complex Analysis Table OS Word
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {a b : Axis}

/-- point order important: upper FIRST, second origin -/
def pair (A B : S.Tag) (x : E4) : ℂ := disc ![A,B] (points ![x,0])
def toPair (x y : L.Plant) := [x,y]

lemma scan (H : S.Hierarchy) (u v : L.Plant) (ho : u.1 ≠ v.1) : S.expect (toPair u v) = pair
    (S.classTokens u.2) (S.classTokens v.2) (u.1-v.1) := by
  rw [← invariance H.translations (show distinct (toPair u v) from locations.mpr (by simp [toPair,ho])) (-v.1)]
  change S.expect [(u.1+-v.1,u.2),(v.1+-v.1,v.2)]=_
  rw [add_neg_cancel,← sub_eq_add_neg,exact_table (show distinct _ from locations.mpr (by simp [ho,sub_eq_zero])) H]
  unfold pair disc; congr 1
  · apply PiLp.ext; intro i; fin_cases i <;> rfl
  funext i; fin_cases i <;> rfl
end YM.Spiral.Ward

#print axioms YM.Spiral.Ward.scan
