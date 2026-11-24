import YM.Profiles.Seeds
import YM.Profiles.Venues
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
variable (N:ℕ)(F:Film c N I E)(p:I→Bool)(w:I→ℝ)(o:I→Site c)(G: Patron.Rail c N D')
namespace GreenCap
open Kites
local notation "S"=> Spine I
local notation "A"=> Keys c N
local notation "K"=> scaler (Keys c N) w
noncomputable def scales: Film c N I E:=⟨F.addr,F.z,fun i U=> K (F.mark i U)⟩
local notation "R"=> scales N F w
local notation "M" i=> ∏ j∈F.z i,(w j:ℂ)
local notation "V₀" i=> ∏ j∈F.z i,|w j|
variable (hF:F.Beat N o p t)
include hF
lemma bodyQ(i:E)(U:Grid c): (R).mark i U=(M i) • F.mark i U:= stamen _ p _ _ _ (hF.budget ..|>.1)
lemma scaled : Film.Beat N o p (R) t :=by
   refine ⟨hF.commits,hF.spark,fun i=>(K).toLinearMap.toContinuousLinearMap.measurable.comp (hF.matters _),fun i V Z he h=> congr_arg (K) (hF.reads i V Z he h), fun i U G=>?_,fun i U hx=>hF.mask _ _ (fun ht=> hx ((congr_arg (K) ht).trans (map_zero _))),fun i U=>?_⟩
   · change _=(R).mark i U; rw [bodyQ N F p w o hF,bodyQ N F p w o hF,map_smul,hF.color]
   rw [bodyQ N F p w o hF]; have ht:=hF.budget i U; refine ⟨?_,?_⟩; change Polite p (F.z i) ((M i) • _); exact Polite.smooch ht.1 _; exact clad.scale ht.2 _
lemma coupons (hp:F.Stock N k α β v κ w)(hv:0 < v): (R).Stock N k α β v κ (fun _=>1):=by
   obtain ⟨g,hX,hU⟩:=hp.price; refine ⟨fun i=>(V₀ i)*g i,fun i U=>?_,?_⟩
   · have ht(i):‖(M i)‖=V₀ i:=by simp only [Complex.norm_real, Real.norm_eq_abs, norm_prod] 
     unfold Film.glyph; rw [bodyQ N F p w o hF,map_smul, Creek.load_scale,ht]; exact mul_le_mul_of_nonneg_left (hX i U) (Finset.prod_nonneg fun i _=> abs_nonneg _)
   have hff: Film.fares N (R) (fun i=>(V₀ i)*g i) (fun _=>1) α=Film.fares N F g w α:=by unfold Film.fares taxed; simp only [abs_one,prod_const_one,one_mul]; rfl
   rw [hff]; exact hU
omit hF
lemma cone (u:EvenA c N): K (rootR S A u)= rootR S A u:=Subtype.ext (by exact tarfib A w _)
variable (V:Grid c)(hV:Summable fun i=>‖F.mark i V‖)(hG:Summable fun i=> ‖G.warp i V‖)
-- omit hF -- but cone included hF. edit.
include hG hV
lemma tickets : Film.reports N (R) G t V= K (Film.reports N F G t V):=by
      let k:= K; let x:=Film.addressSets N F G; let f i:=Film.spruced N F G i V; have hS : Summable fun i=> ‖f i‖:=Summable.sum _ (Film.payable (rootR S A).toLinearMap.toContinuousLinearMap hG) hV; unfold Film.reports; rw [show k (∑' i,Plate.roof x f (RG.flags _ V) i)=_ from Film.stamps x f (RG.flags t V) k hS]; have he:(fun i=> Film.spruced N R G i V)= k ∘ f:=by
          funext i; rcases i with i|i; exact (cone N w _).symm; rfl
      rw [he]; rfl
omit hG hV
lemma shade (Ax:Type)[Fintype Ax](u:Finset I)(x: Patio (Ax⊕Spine I)) : scaler Ax w (shutter Ax u x)=shutter Ax u (scaler Ax w x):=by
    apply pluckVisible; intro i; simp_rw [Cupola.shutter,Cupola.pulse]; exact smul_comm ..
end GreenCap
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.GreenCap.tickets
#print axioms YM.MassiveQCD.Sample.GreenCap.coupons
