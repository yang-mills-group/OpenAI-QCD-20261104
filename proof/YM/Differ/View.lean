import YM.Profiles.Eloquence
/-!
 # Single arrangements in actual Units. Caps pre weights on pointed/reference layouts.P composed with updates.Yes.
   No explicit global identity in this run of the one-source cone. (All labels including that one use actual indicators; net also pays that weight). 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a b θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
-- Step references. No common label-union across books demanded. `w x partial` eq at outgoing health.Loosen.a' . Seat.S. set covering.
variable (x:Label d) (q:Bool) (Pt:BudgetPoint)
section
-- initial inheritance.Use Rite not split metadata. Body artifact.Arc χ.
variable (z:ℝ)(F:CentreFrame (c:=c) Pt v x q A b (r+1) I Empty) (V:Grid c)
-- whole expected unmarked pre.Permeant.
variable [Fintype I]
noncomputable def spineV (V:Grid c):QCD.Lat.Fields c 6:= (∑ j : Jars d ⊕ I,(ritual F).fill j V)
#check spineV
-- explicit formula for free generation cylinder.
local notation "Φ" => spineV
local notation "R₀" => goldM q
local notation "F₁"=> ritual F
local notation "sΞ" P => (byG F P)
lemma openW : (∑ j:Jars d,(F₁).fill (.inl j) V)= Orientation.graphs (c:=c) d A b x V:=by
   let f :Label d →ₗ[ℂ] Alg (Keys c 6):=(ContinuousMap.evalCLM ℂ V).toLinearMap.comp ((Realize.placed (A.t d) c b).comp (A.lead d)); change ∑ j:Jars d,f (gradeCut d j.val x)= f x; rw [← map_sum,sumCut]
lemma spineView : spineV A b x q Pt F V= Orientation.graphs (c:=c) d A b x V+∑ j:I,F.p.fill j V:=by unfold spineV; rw [Fintype.sum_sum_type,openW]; rfl -- bind order
-- exact index.p behaviour under normalization byG
lemma byArr (u:ℂ) (j:Jars d⊕ I) : (ritual (byG F u)).addr j= (ritual F).addr j:=by cases j <;> rfl
lemma byFill (u:ℂ) (j:Jars d⊕ I) : (ritual (byG F u)).fill j= u • (ritual F).fill j:=by
    cases j with
    | inr i=>rfl
    | inl i=> funext V; change graphs _ _ _ (gradeCut d i.val (u • x)) _=u • _; rw [map_smul]; exact DFunLike.congr_fun (map_smul ((Realize.placed (A.t d) c b).comp (A.lead d)) u _) V
lemma byMask (u:ℂ) (j:Jars d⊕ I): (ritual (byG F u)).roll.mark j= u • (ritual F).roll.mark j:=by
    funext V; apply Subtype.ext; let g:=stake (Keys c 6) (goldM q); change g (_)=u • (g _); change g ((ritual (byG F u)).fill j V)=u • _; rw [byFill,Pi.smul_apply,map_smul]
lemma byWhole (u:ℂ) : spineV A b (u • x) q Pt (byG F u)=u • spineV A b x q Pt F:=by funext i; unfold spineV; rw [Pi.smul_apply,smul_sum]; simp_rw [byFill]; rfl
structure Courtesy (D C:ℝ): Prop where
   paid :∃ f:Jars d ⊕ I→ℝ,(∀ i,0 ≤ f i)∧(∀ i V, Creek.load (fun _=>v) ((ritual F).fill i V) ≤ f i)∧ (∑ i: Jars d⊕ I, f i*Real.exp (D*coverNumber Pt.B ((ritual F).addr i).support)) ≤ C
lemma due (h:Courtesy A b x q Pt F a C)(u:ℂ): Courtesy A b (u • x) q Pt (byG F u) a (‖u‖*C):=by
    obtain ⟨g,hg,hv,hP⟩:=h.paid; refine ⟨fun i=> ‖u‖*g i,fun i=>mul_nonneg (norm_nonneg _) (hg _),fun i V=>?_,?_⟩ -- nested.Exists costs
    · rw [byFill,Pi.smul_apply,Creek.load_scale]; exact mul_le_mul_of_nonneg_left (hv i V) (norm_nonneg _)
    simp_rw [byArr,mul_assoc,← mul_sum]; exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
end
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.byArr
#print axioms YM.Massive.Poised.Plans.Stamp.byWhole
#print axioms YM.Massive.Poised.Plans.Stamp.due
