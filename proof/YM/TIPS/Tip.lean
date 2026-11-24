import YM.TIPS.Layer
import YM.Cape.Arch
/-! # regenerate publication tip for attaching at the same stage -/
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
variable {I J E D U :Type}[Fintype I]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
namespace Taxing
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j N:ℕ}
variable (p:I→Site c) (q:I→Bool) (F: Patron.Rail c (ample N I) E) (hf:Wage.Tip N p q F P v α t) (hV:0<v)
local notation "H!"=> faultK N p v F
local notation "K"=> Keys c N
lemma plank (i:E)(U:Grid c): Cove.light K ((H!).warp i U)= pluck K ∅ (withdraw N p v (F.warp i U)):= revive ..
include hf hV
lemma spored: Pill (H!) P.threshold v P.B α t:=by
    have hU:=hf.tilt.uses; let L:= (vacR (Spine I) (Keys c N)).comp (withdraw N p v); let F':=H!; refine ⟨⟨fun i X Y hx h=>congr_arg L (hU.uses i X Y hx h),fun i=>L.toLinearMap.toContinuousLinearMap.measurable.comp (hU.reads i),?_,fun i U h=>hU.buys i U (fun e=> h ((congr_arg L e).trans (map_zero L)))⟩,?_,?_⟩
    · intro i U; change Cove.light K (F'.warp i U) ∈ _; rw [plank p F]; exact Cupola.pennied N p _ _ _ _ (hU.role i U)
    · intro i U g; let V:= gauge g U; let C:= parcelColor N g I
      let y:= withdraw N p v (F.warp i V); have ht:= hf.fits i V; let W:= withdraw N p v (F.warp i U)
      have hp: W=C y:=Eq.trans (congr_arg (withdraw N p v) (Eq.trans (Subtype.ext (hf.tilt.pigment i U g)).symm ((congr_arg (sways (Lat.rotates (ample N I) g)) ht.spark.symm).trans (all_color N p v q g y ht.applies).symm))) (Cupola.home N p v hV (C y))
      change slots N _ (Cove.light K (F'.warp i V))= Cove.light K (F'.warp i U); rw [plank p F i V,plank p F i U, show withdraw N p v (F.warp i U)=_ from hp]; exact (partColor N I g y _).symm -- signature
    obtain ⟨f,hX,hq⟩:= hf.tilt.sold.cost; refine ⟨f,hX,fun i U=>?_⟩; rw [Loom.pulse,plank p F]; exact (Well.pin _ hV (hf.fits i U)).trans (hq _ _)
omit hf hV
open QCD.Cove QCD.Ruby
lemma billing (N:ℕ)(Y: Patron.Rail c N J)(X: Patron.Rail c N D)(M:Film c N I E)(U:Grid c)(h: Correspond Y X)(hM:Summable fun i=>‖M.mark i U‖): Film.reports N M Y t U=Film.reports N M X t U:=by
    let R:= Ribbon.Spine I; let Z:= Keys c N; let f i:= M.mark i U; let F:=rootR R Z
    suffices h0:∀ (J:Type) (X: Patron.Rail c N J)(hp: Summable fun i=>‖X.warp i U‖), Film.reports N M X t U=∑' i, Plate.roof id (fun w:Cove.Hat c=> F (coin X.addr (fun i=>X.warp i U) w)+coin M.addr f w) (flags t U) i by rw [h0 J Y (h.pays U),h0 D X (h.coins U)]; apply tsum_congr; intro i; simp_rw [h.governs _ U]
    intro J P hp; have hz : Summable (fun i:J⊕ E=> ‖Film.spruced N M P i U‖):=Summable.sum _ (Film.payable F.toLinearMap.toContinuousLinearMap hp) hM
    unfold Film.reports; rw [catalogue (Film.addressSets N M P) (fun i=>Film.spruced N M P i U) (flags t U) hz]; apply congr_arg (fun x:Cove.Hat c→ Patio (Z⊕R)=>∑' i,Plate.roof id x (flags t U) i); funext B
    exact (Film.coin_merge P.addr M.addr (F ∘ (fun i=> P.warp i U)) f (Film.payable F.toLinearMap.toContinuousLinearMap hp) hM B).trans (congr_arg (fun y=>y+coin M.addr f B) (readycoin P.addr (fun i=>P.warp i U) B F.toLinearMap.toContinuousLinearMap hp))
end Taxing
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Taxing.spored
#print axioms YM.MassiveQCD.Sample.Taxing.billing
