import YM.Eole.Land
import YM.Pollen.Linda
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
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
variable {D E:Type}{n:ℕ}{c:Side}{v a b t k:ℝ}
variable (q:I→Bool)(W:Bloc I J)
namespace Bloc
local notation "U"=>W.flag q
local notation "Z"=>Keys c n
local notation "X"=>Patio (Z⊕Spine I)
local notation "Y"=>Patio (Z⊕Spine J)
local notation "T"=>Stitch.Tablet.credits
local notation "LK"=>lane Z q W
lemma value_norm (s:Finset J)(hv:0<v)(x:X)(hx:Polite q (W.plant s) x) : T v ((lane (Keys c n) q W s) x)=T v x:=by
    let l:=s.toList; have hp:s=l.toFinset:=(toList_toFinset s).symm
    have h(Q:I→Bool)(s:Finset I)(i:List I)(h:s=i.toFinset)(hp:i.Nodup)(x:X)(hx:Polite Q s x): load (fun _=>v) (numbered Q Z i.get x)=T v x:=by
         rw[Stitch.Tablet.polite_bill s _ hx hv]; unfold numbered; rw [ContinuousLinearMap.smul_apply,load_scale, ← decal,← h, (arm_bill Q _ (List.nodup_iff_injective_get.mp hp)).1,one_mul]; rfl
    -- duplicate
    let y:= LK s x; have hY:load (fun _=>v) ((numbered U Z l.get) y)=T v y:=by
         rw[Stitch.Tablet.polite_bill s y (overlay Z q W s x) hv]; unfold numbered; rw [ContinuousLinearMap.smul_apply,load_scale, ← decal,← hp,(arm_bill U _ (List.nodup_iff_injective_get.mp s.nodup_toList)).1,one_mul]; rfl
    refine hY.symm.trans ?_; have hz:W.plant s=(W.twins l).toFinset:=by rw [W.stowed l,← hp]
    rw [show numbered _ _ l.get y=_ from decalEq _ _ _ _ s.nodup_toList x]; exact h q _ _ hz (W.tightened _ s.nodup_toList) _ hx
lemma colored (s:Finset J)(x:X)(g:Lat.Frame c) : (lane Z q W s) (parcelColor n g I x)=parcelColor n g J (lane Z q W s x):=by
    let L:=s.toList; refine singleton_eval Z U L _ _ ?_ ?_ s.nodup_toList ?_
    · simpa [L] using overlay Z q W s (parcelColor n g I x)
    · simpa [L] using Cupola.vault n U s _ g (overlay Z q W s x)
    change numbered U Z L.get (sector Z q W L _) =_
    have hz(i:List J)(x:Y): numbered U Z i.get (parcelColor n g J x)= slots n g (numbered U Z i.get x):=by unfold numbered; rw[ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,map_smul,partColor]
    rw [decalEq Z q W L s.nodup_toList,hz,show numbered U Z L.get _ =_ from decalEq Z q W L s.nodup_toList x]; unfold numbered; rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,map_smul,partColor]
lemma forecast (s:Finset J)(o':I→Site c)(o:J→Site c)(S:Support c)(x:X)(h:Stitch.lights (W.plant s) S o' q x) : Stitch.lights s S o U ((lane Z q W s) x):=by
    let l:=s.toList
    have he:=(overlay Z q W s x); refine ⟨he, fun i=>?_⟩ -- clad dest.L.H
    by_cases hx:i=burst U s; · rw[hx]; change pluck Z (burst U s) ((lane Z q W s) x) ∈ Creek.region (limits S); rw[show burst U s=burst U l.toFinset by rw[toList_toFinset],show LK s=sector Z q W l from rfl,liver]; apply Subalgebra.smul_mem; unfold numbered; rw[ContinuousLinearMap.smul_apply]; exact Subalgebra.smul_mem _ (h.2 _) _ -- binder
    rw [he.spectral i hx]; exact Subalgebra.zero_mem _
end Bloc
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.forecast
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.colored
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.value_norm
