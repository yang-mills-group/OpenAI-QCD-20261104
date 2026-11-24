import YM.Ward.Plants
import YM.Gust.Cav.Words
import YM.Gust.Cav.D
import YM.Gust.Cav.Light
/- Variant of YM.Ward.Plants, for Spiral register. -/



/-!
# Exact singleton ket over any germ of a point. Connect Table.Tag derivatives.

Interior strict only. Plants/mirrors use exact tensor adjoint convention.
Projection kernel identities needed for linking. Banach 1D smooth without
helper representation assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spiral.Ward
open Function Set Filter Complex Analysis OS Word
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {a b : Axis}

def expose (t : S.Tag) : L.Token := ⟨t.1,S.representative _ t.2⟩
@[simp] theorem sends_back (t : S.Tag) : S.classTokens (expose t)=t := by change ⟨t.1,S.project _ (S.representative _ t.2)⟩=t; rw [S.rep]

lemma resolve {p : L.Plant} {v : L.Word} (S : Table L) : S.expect (p::v) =
    S.read (Points.cons p.1 (positions v)) (Fin.cons p.2 (tokens v)) := by
  have hv : realize (Fin.cons p.2 (tokens v)) (Points.cons p.1 (positions v))=p::v := by
    unfold realize; rw [List.ofFn_succ]
    simp only [Points.cons,points_apply,Fin.cons_zero,Prod.mk.eta]
    congr 1
    simp only [Fin.cons_succ]
    exact rebuilt v
  conv_lhs => rw [← hv]
  exact S.readAt _ _

lemma exact_table {p : L.Plant} {v : L.Word} (h : distinct (p::v)) (ht : S.Hierarchy) : S.expect (p::v) = S.useAt S
    (Points.cons p.1 (positions v)) (Fin.cons (S.classTokens p.2) fun i => S.classTokens (tokens v i)) := by
  rw [resolve,← S.at_project S ht.laws.toSymmetric (fun _ => le_rfl) ?_]
  · apply congr_arg; funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← Word.realized (v := Fin.cons p.2 (tokens v))]
  suffices he : realize (Fin.cons p.2 (tokens v)) (Points.cons p.1 (positions v))=p::v from he ▸ h
  unfold realize; rw [List.ofFn_succ]; simp only [Points.cons,points_apply,Fin.cons_zero,Prod.mk.eta]
  congr 1; simp only [Fin.cons_succ]; exact rebuilt v

lemma disjoint_table {p : L.Plant} {v : L.Word} (ht : distinct (p::v)) : Points.cons p.1 (positions v) ∈ conf _ := by
  have hw : positions (p::v)=Points.cons p.1 (positions v) := by
    apply PiLp.ext; intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons, positions]
  rw [← hw]; exact ht
variable (W:DiffPlan S)
def rise (b : Axis) (p : S.Tag) : S.Tag := ⟨p.fst+1,W.deriv p.fst b p.2⟩
end YM.Spiral.Ward

