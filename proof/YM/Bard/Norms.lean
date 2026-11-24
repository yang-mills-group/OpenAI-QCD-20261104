import YM.Profiles.Posy
import YM.Mills.Vivid
import YM.Profiles.Wreaths
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
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace Posy
open NormedSpace Stew Ruby Quills -- h.OK
variable {U:Type}(Y:Reel c 6 I E)(F:Film c 6 I J)(K: Patron.Rail c 6 U)(p:I→Bool)(o:I→Site c)
local notation "A"=> Keys c 6
local notation "B"=> Spine I
variable (W:Grid c)
variable (F':E→ℝ) {v₀:ℝ}
local notation "α₁"=> F'
lemma sustain (h:SC.Valve Y o p v v₀ k α t F')(ht:∀ i,1 ≤ F' i) (hv:1≤ v)(hα:0 ≤ α) : ‖Reel.rope Y v₀ W‖ ≤ (Fintype.card (Site c):ℝ)*t:=by
    obtain ⟨u,hU,hP⟩:=h.back; let f i:= F' i * u i; let g i:= Y.mist v₀ i W; have ht(i): ‖g i‖ ≤ f i:=by
         have he: ‖g i‖ ≤ u i:= (loaded (g i).val (Stitch.Tablet.chip v A B) (fun j=>by rcases j with j|j; exact hv; exact le_rfl)).trans (hU i W)
         exact he.trans (le_mul_of_one_le_left ((norm_nonneg _).trans he) (ht i))
    have hh:= QCD.Acre.Rails.spiritual f _ hP (fun i=> ⟨_,(Y.addr i).anchor⟩) hα (fun i=>(norm_nonneg _).trans (ht i)); let g':=budget_mono hh (fun i=> norm_nonneg _) ht; exact (norm_tsum_le_tsum_norm g'.2.1).trans g'.2.2
variable {U' :Type} (F:Film c 6 I U')(G:Grid c→ EvenA c 6)
variable {δ β' h w:ℝ}
lemma sustainedV (h0: SC.Valve Y o p v v₀ k α t F')(ht:∀ i,1≤ F' i)(hv:1≤v)(hα:0≤α) (hV:Kites.Quits K k h β w v)(hk:F.Stock 6 k δ α v Γ (fun _=>1))(hF:F.Beat 6 o p v₀)(hg:1 ≤ β)(hγ:1≤δ) (he:0≤ w) : -- Quits not right parameters.want l:ℝ instead ℕ and he distinct.B.
   ‖relativeE 6 Y F K G v₀ W‖ ≤ ‖NormedSpace.exp (G W)‖ * Real.exp ((Fintype.card (Site c):ℝ)*(t+(h+Γ))):=by
    let X:= rootR (Spine I) (Keys c 6); let T:= G W; let y:= Reel.rope Y v₀ W
    have hh: exp (X T+y)=X (exp T)*exp y :=by rw [exp_add,NormedSpace.map_exp X X.toLinearMap.toContinuousLinearMap.continuous];
    have hp:= exp_price y|>.trans (Real.exp_monotone (sustain Y p o W F' h0 ht hv hα))
    have hn:= (norm_mul_le (X (exp T)) (exp y)).trans (mul_le_mul (lightCost _|>.le) hp (norm_nonneg _) (norm_nonneg _)); unfold relativeE; rw [hh]; apply (norm_mul_le ..).trans ((mul_le_mul hn (filmP p o W F K hV hk hF hg hγ he hα hv) (norm_nonneg _) ((norm_nonneg _).trans hn)).trans (?_)); apply le_of_eq; rw [mul_assoc, ←Real.exp_add,mul_add,mul_add,mul_add]
end Posy
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Posy.sustainedV
