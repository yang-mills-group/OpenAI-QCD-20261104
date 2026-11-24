import YM.QCD.Creek.Crest
import YM.QCD.Creek.Flags
import YM.QCD.Fork.Base
/-! # even subalgebra. Keep calculations in c-lifted magmas finite.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Grass Function Creek Metric NormedSpace
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {A B C: Type*} [Fintype A][Fintype B]
def roomA (A:Type*) [Fintype A] : Subalgebra ℂ (Alg A) where
 carrier := {x|Plus x}
 mul_mem' := Hom.mul (p:=false) (q:=false)
 one_mem' := show Plus _ from map_one _
 add_mem' := Hom.add (p:=false)
 zero_mem' := Hom.zero false
 algebraMap_mem' x := show Plus _ from AlgHom.commutes _ _

abbrev Patio (A:Type*) [Fintype A]:=↥(roomA A)
instance : CommRing (Patio A) where
 __ := (inferInstance : Ring (Patio A))
 mul_comm x y := Subtype.ext (show Commute _ _ from (Plus.central (y.property:Plus y.val) x.val)).eq
-- keep Banach
lemma shutA (A:Type*) [Fintype A] : IsClosed (roomA A:Set (Alg A)):= isClosed_eq (grade (A:=A)).toLinearMap.continuous_of_finiteDimensional continuous_id -- syntax?
instance : CompleteSpace (Patio A):= by exact (shutA A).completeSpace_coe
instance : NormedCommRing (Patio A) where
 __ := (inferInstance : CommRing (Patio A))
 __ := (inferInstance : NormedRing (Patio A))
instance : NormedAlgebra ℚ (Patio A):= .restrictScalars ℚ ℂ _
instance : NormedAlgebra ℝ (Patio A):= .restrictScalars ℝ ℂ _ -- real lift
instance : NormOneClass (Patio A):=⟨norm_one (α:=Alg A)⟩

instance : MeasurableSpace (Alg A) := borel _
instance : BorelSpace (Alg A) := ⟨rfl⟩
-- coe lemmas
abbrev light (A : Type*) [Fintype A]: Patio A→ₐ[ℂ] Alg A := (roomA A).val
lemma light_eq (x: Patio A) : light A x=x.val:= rfl
lemma bright (x: Patio A): Plus (light A x):=x.property
@[fun_prop] lemma lightC (A:Type*)[Fintype A]: Continuous (light A):= continuous_subtype_val
lemma light_exp (x: Patio A): light A (exp x)=exp (light A x):= map_exp (light A) (lightC A) x

def car (F:Alg A→ₐ[ℂ] Alg B)(h:∀ x, Plus x→ Plus (F x)): Patio A→ₐ[ℂ] Patio B where
 toFun x:= ⟨F (light A x), h _ (bright x)⟩
 map_mul' x y:=Subtype.ext (map_mul F _ _ |>.trans (by rfl))
 map_one':=Subtype.ext (map_one F)
 map_zero':=Subtype.ext (map_zero F)
 map_add' x y:=Subtype.ext (map_add F _ _ |>.trans (by rfl))
 commutes' x:=Subtype.ext (AlgHom.commutes F x)

lemma carriage (F:Alg A→ₐ[ℂ] Alg B)(h:∀ x, Plus x → Plus (F x))(x: Patio A): light B (car F h x)=F (light A x):=rfl

end YM.QCD.Cove
