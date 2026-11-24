import YM.Eole.Lane
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
variable (A)(q:I→Bool) (W: Bloc I J) (l: List J)
namespace Bloc
local notation "Γ"=> W.plant
local notation "u"=> W.flag q
local notation "X"=> Patio (A⊕Spine I)
local notation "Y"=> Patio (A⊕Spine J)
local notation "T"=> lane A q W
noncomputable def sparC : Patio (A⊕Spine I)→L[ℂ] Patio (A⊕Spine J) :=∑ s:Finset J,T s
local notation "Ω"=> sparC A q W
lemma evanesce (Q:I→Bool)(L:List I)(s:Finset I)(he:s≠ L.toFinset)(x:X)(h:Polite Q s x) : numbered Q A L.get x=0:= by unfold numbered; rw [ContinuousLinearMap.smul_apply, ← decal,show pluck _ _ _ =0 from h.spectral _ ((burstUnique Q).ne he.symm), smul_zero]
lemma vanishes (s:Finset I)(t:Finset J)(x:X)(hx:Polite q s x)(he:s ≠ W.plant t): T t x=0:=by
    let l:=t.toList; apply Subtype.ext; change ((sector A q W l) x).val=0; rw [barrel _ _ _ _ (nodup_toList t), evanesce _ _ _ s (by rw[W.stowed,toList_toFinset]; exact he) _ hx, map_zero,zero_mul]
lemma single_plant {s:Finset J}(x:X)(hx:Polite q (Γ s) x) : (Ω) x=T s x:=by
    rw[sparC,_root_.sum_apply,sum_eq_single s _ (by simp)]; intro i _ hi; exact vanishes A q W _ _ x hx fun hp=>hi (by rw[← W.planted i,←hp,W.planted])
lemma all_seed (p:Finset I)(x:X)(hx:Polite q p x)(hz: W.plant (W.core p) ≠ p) : Ω x=0:=by
     rw[sparC,_root_.sum_apply]; exact sum_eq_zero fun i _=> vanishes A q W p i x hx fun ht=> hz (by rw[ht,W.planted])
lemma core_mem (x:X) : ValidPieces A u univ (Ω x):=by rw [sparC,_root_.sum_apply]; exact ValidPieces.cost univ _ (fun i _=>ValidPieces.role _ (overlay A q W i x) (subset_univ _))
lemma reading (x:X)(hl:l.Nodup) : numbered u A l.get (Ω x) = numbered q A (W.twins l).get x:=by
    rw [sparC,_root_.sum_apply,map_sum,sum_eq_single l.toFinset]; · rw [arranged A q W l hl]; exact decalEq A q W l hl x
    · intro i _ hi; exact evanesce A u l i hi _ (overlay A q W i x)
    simp
variable (y: Y)
lemma planted_value (x:Patio A) : lane A q W ∅ (rootR (Spine I) _ x)= rootR (Spine J) _ x:=by
    rw[lane,toList_empty]; apply Subtype.ext; rw[barrel _ _ _ _ (by simp),show W.twins []=[] from rfl, emptyN]; let f:=rootR (Spine I) A; have he:pluck A (∅:Finset (Spine I)) (f x)=x.val:=by change scrape A ∅ (Ribbon.fiber (Spine I) _)=_; rw[← quiet,quid];rfl
    rw[show pluck _ _ _=x.val from he,show armature u [].get=1 by simp[armature],map_one,mul_one]; rfl
-- root
end Bloc
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.reading
