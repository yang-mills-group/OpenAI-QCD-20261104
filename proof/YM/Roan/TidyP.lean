import YM.Roan.Priory
import YM.Avian.Wards
import YM.Roan.Rule
import YM.Clink.Brass
import YM.Kwick.Vale
import YM.Roan.Ode
import YM.Lapin.Spark
/-! End read at reference upper Hop boot.Several charts transfer.X near arbitrary.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Pane Tawny.BendR
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
/- Need Shelf.Guru.Bind at references. Keep full Tally + price lower.S
-/
variable {S:Scheme}{R:Side} (A:Run S N R 6) (q:ℕ)(T:TaperHol)
variable (W:Axis→ℕ→ℝ)(v w:ℕ→ℝ)(B:ℕ→BudgetPoint)(d ℓ:ℕ)
variable (u α a κt K b δ H:ℝ)(P:Axis → Cover → Insertion (S.side R q) 6)(f:ℕ→RawVec 10)
-- projection cost action.F
open Plans.Stamp Seals Onyx Tarn Tarn.Choir LinearMap
lemma taggedT : ‖(LinearMap.id : Label 10→ₗ[ℂ] Label 10).toContinuousLinearMap‖=1:=by
         cases subsingleton_or_nontrivial (Label 10) with
         | inr h=> exact ContinuousLinearMap.norm_id
         | inl hh=>
             exfalso; haveI: Subsingleton ↥(RawVec 10):= inferInstance
             have h:Module.finrank ℂ ↥(RawVec 10)=45:= Onyx.rawV; rw [Module.finrank_zero_of_subsingleton] at h; omega
variable (F:Tarn.Choir)
local notation "Pc"=> bits F
lemma ranks_p (S T:ℝ)(hp:Surjective ((((compass 1 S).prod (point T 1 S)).domRestrict ((bits F).ker)))): Worth F:=by
         refine ⟨(↑(1*S^2:ℝ):ℂ) • pay1, (↑(T*(1*S^2):ℝ):ℂ) • pay2,fun x=>?_⟩; obtain ⟨t,h⟩:=hp x; exact ⟨t,h⟩
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.ranks_p
#print axioms YM.Massive.Patria.Gall.Cahoots.taggedT
