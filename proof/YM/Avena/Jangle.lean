import YM.Parishes.Braid
import YM.Cardinal.Radome
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
lemma climbing (hp:TypeBeta u w w' v a ε' ε₁ P Q x y): W₁ ≤ ε₁ + a * Sd:=by
    obtain ⟨g,hr,hw⟩:=hp.paid
    have hQ := wealth_plus (y-∑ i,g i) (∑ i,g i) Q w'
    rw [sub_add_cancel] at hQ
    apply hQ.trans
    apply add_le_add hw
    have h:wealth (∑ i,g i).val Q.threshold w' ≤ ∑ i,wealth (g i).val Q.threshold w':=by
        have H:=total_wealth (s:=Q.threshold) (e:=w') g (hasSum_fintype g).summable
        rw [tsum_fintype,tsum_fintype] at H; exact H
    apply h.trans; unfold toted; rw [Finset.mul_sum]
    apply sum_le_sum; intro i _; rw [←mul_assoc]; exact (hr i).1
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.climbing
