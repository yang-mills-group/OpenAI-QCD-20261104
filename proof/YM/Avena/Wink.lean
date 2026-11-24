import YM.Avena.Jangle
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c f L:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
variable (x y:Label d) (q:Bool) (Pt:BudgetPoint)
set_option quotPrecheck false
namespace Stair
variable {w w' a b c₁ d₁ e y₃ ε ε' ε₁:ℝ}{Pt P Q R:BudgetPoint}
local notation "Wd" => fun (i:Jars d)=> u^(weightJ i)*princS x i P w
local notation "Sd"=>toted u x P w
local notation "W₁"=>wealth y.val Q.threshold w'
local notation "Wi"=>wealth x.val P.threshold w
variable {x y}
namespace Cabin
lemma wNorm (d:ℕ): ∃ C J:ℝ,1≤ C ∧ 1≤J ∧ ∀ (t v : ℝ)(x:Label d), ‖dimming t v d x‖ ≤ C * wealth x.val t v ∧ wealth x.val t v ≤ J * ‖dimming t v d x‖:=by
    obtain ⟨A,hA,h⟩:= payFrame (Module.finBasis ℂ (Label d)); let Z : Rings d→ Label d→L[ℂ]ℂ:=fun i=> ((Stative.coord i.val).comp (labels d).subtype).toContinuousLinearMap
    let J:ℝ:=∑ i:Rings d, ‖Z i‖; refine ⟨A,max J 1,hA,le_max_right ..,fun t v x=>⟨h x t v,?_⟩⟩; apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _)); unfold wealth J; rw [sum_mul]; apply sum_le_sum; intro i _; exact (Z i).le_opNorm (dimming t v d x)
set_option maxHeartbeats 600000 in
lemma normBound (P:BudgetPoint)(v:ℝ)(hv:0<v)(d:ℕ): ∃ J:ℝ, 1≤ J ∧∀ x:Label d, ‖x‖ ≤ J*wealth x.val P.threshold v:=by
      obtain ⟨C,K,hC,hK,h⟩:= wNorm d; have hu:= widthPoly P.threshold_pos hv d; let Q:= LinearEquiv.ofBijective (dimming P.threshold v d) ⟨hu,(LinearMap.injective_iff_surjective).1 hu⟩; let T:= Q.symm.toLinearMap.toContinuousLinearMap
      let J:= max 1 (‖T‖*C); refine ⟨J,le_max_left 1 _,fun x=>?_⟩; have hx:T (Q x)=x:= Q.symm_apply_apply _; have hg:= T.le_opNorm (Q x); rw [hx] at hg; have hL: ‖Q x‖ ≤ C * wealth x.val P.threshold v:=(h P.threshold v x).1; apply hg.trans; apply le_trans (mul_le_mul_of_nonneg_left hL (norm_nonneg T)); rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right 1 _) (wealth_ge ..)
end Cabin
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.Cabin.normBound
