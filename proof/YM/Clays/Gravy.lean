import YM.Clays.Grant
import YM.Portland.Hunk
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
open Stags QCD.Kites Acre Acre.Rails
variable {c:Side}{a H C V W v x y:ℝ}{J E I K:Type}[Fintype I] {Pt:BudgetPoint} {i m k:ℕ}
variable (p:I→Site c)(q:I→Bool)(F: Reel c 6 I E)(hf:E→ℝ)
variable (L:Side)(T: Teller su)
namespace Basal
-- K installation permit. activated seed earn.Term.Body.Stage only
local notation "iC"=> (20/256:ℝ)
local notation "i₀"=> (18/256:ℝ)
local notation "k₀"=> (14/256:ℝ)
local notation "q₀"=> (1/256:ℝ)
local notation "W₀"=> (8/256:ℝ)
variable {B:ℕ}
open QCD.Ruby Push.AbsoluteSums.Trees
structure Dough (L:Side)(F:ℕ)(x:ℝ):Prop where
    legacy : StackK (highR L x) (taxK L x 2) (taxK L x (9/5)) (20/256) (18/256) (21/256) 1
    pose : StackK (highR L x) (taxK L x (9/5)) (taxK L x (8/5)) (18/256) (14/256) (19/256) 1
    recolor(c:Side)(I E:Type)[Fintype I](P:BudgetPoint)(o:I→Site c)(q:I→Bool)(A:Set (Finset I)) (Y:Patron.Rail c (ample 6 I) E)(t:ℝ):P.B=highR L x→Fires o F→(∀ i∈ A,Spaced o i P.B)→ Wage.Tip 6 o q Y P t (14/256) (taxK L x (8/5)) → 0<t→Film.Stock 6 (Film.publication 6 o q Y A t) P.B (taxK L x 1) (8/256) t (taxK L x ((2-1)/2))⁻¹ (fun _=>1)
lemma lump (K:ℕ):∀ᶠ x in atTop,Dough L K x:=by
    filter_upwards [Sail.pulseBottle L (9/5) 2 i₀ (iC-i₀) (by norm_num) (by norm_num) (by norm_num) (by norm_num), Sail.pulseBottle L (8/5) (9/5) k₀ (i₀-k₀) (by norm_num) (by norm_num) (by norm_num) (by norm_num),Film.Surplus.grantKX L (3*q₀) (8/5) 1 ((2-1)/2) K (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _=>1) (Rate.const 1) W₀] with i hi hh hv
    rw [show i₀+(iC-i₀)=iC from by norm_num, show iC+q₀=21/256 from by norm_num] at hi; rw [show k₀+(i₀-k₀)=i₀ from by norm_num, show i₀+q₀=19/256 from by norm_num] at hh
    refine ⟨hi,hh,?_⟩; intro c I E _ P o q A Y t hB hF ht hP hz; rw [hB]; have hw: Pill Y P.threshold t (highR L i) (W₀+2*(3*q₀)) (taxK L i (8/5)):=by rw [←hB,show W₀+2*(3*q₀)=k₀ from by norm_num]; exact hP.tilt
    exact hv t 6 c E I Y A o q P.threshold _ hF (fun j hj=> (show Spaced o j (highR L i) from hB ▸ ht j hj)) hw hP.fits (fun _=>le_rfl) hz
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.lump
