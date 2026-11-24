import YM.Eole.Serene
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
variable (A)(W:Bloc I J)(q:I→Bool)(x:I→ℝ)
namespace Bloc
local notation "Φ"=> plant W
local notation "Z"=> A⊕Spine I
local notation "P"=> W.flag q
local notation "Jq"=>sparC A q W
local notation "S"=> scaler A x
lemma amounts (y:Patio (A⊕Spine I))(l: List J)(h:l.Nodup): numbered (W.flag q) A l.get ((Jq) (scaler A x y))= (Eole.Gain.uvBirth x (W.plant l.toFinset)) • numbered q A (W.twins l).get y:=by
    rw [reading A q W l (S y) h]; unfold numbered; rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,Cupola.pulse,Cupola.sensed]; rw [← decal,W.stowed]; exact smul_comm ..
lemma match_cost (y z:Patio (A⊕Spine I))(t:Finset J)(h:shutter A (W.plant t) y=shutter A (W.plant t) z): shutter A t (Jq (S y))=shutter A t (Jq (S z)):=by
     simp only [sparC,_root_.sum_apply,map_sum]; apply sum_congr rfl; intro i _; let L:= lane A q W i; rw [stamen_h A P i t _ (overlay A q W i _),stamen_h A P i t _ (overlay A q W i _)]; split; next ho=>
            suffices he:L (S y)=L (S z) from he; let l:= i.toList; refine singleton_eval A P l (sector A q W l _) _ (nice A q W l _) (nice A q W l _) i.nodup_toList ?_; rw [decalEq A q W l i.nodup_toList,decalEq A q W l i.nodup_toList]
            let s:= W.twins l; have ht : crest s.get⊆ W.plant t:=by rw [← decal]; unfold s; rw [W.stowed,show l.toFinset= i from toList_toFinset _]; exact fun k hk=> (W.belongs ..).2 (ho ((W.belongs ..).1 hk))
            unfold numbered; rw[ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,Cupola.pulse,Cupola.pulse]; have hx:= phoenixC A y z (W.plant t) h (burst q (crest s.get)) (fun i hi=> ht (located q (crest s.get) _ hi)); change _ • (_ • pluck A (burst q (crest s.get)) y) = _; rw [hx]
     rfl
end Bloc
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.match_cost
