import YM.Hail.Eff
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical ComplexOrder
open Massive.Tawny Massive.Tawny.Cast Perla Perla.Fore Carnal Rays TableT Drill
open Finset Module LinearMap
local notation "Sx"=> RawTensor 1 8
variable (a b i:Axis)(v:Sx)(hy:v∈ ({v} : Set Sx))(p z:ℂ)(r:Flavor 6→ℂ)
noncomputable def crossH (X:Points 1)(t:Sx)(j: Axis×Axis):ℂ:= moment (fun _:Fin 1=>8) X (fun _ => (t.val j).val)
local notation "H"=> symbS 1
variable (X:Points 1)(hx:X∈conf 1)
include hx
set_option quotPrecheck false
local notation "Vx"=> (moment (fun _:Fin 1=>8) X).toLinearMap 0 0
lemma crossed (u:Sx)(x:Axis×Axis)(hh:H u=H v) : crossH X u x=crossH X v x:= descendant X hx _ _ (fun i=>congr_arg Subtype.val (congr_fun hh x))
lemma crime (h:H v = shore p r+ z • H epi) : crossH X v (a,a)=z:=by
     let s:= flood p r + z • epi; have he: H v= H s:=by rw[h]; unfold s shore; rw[_root_.map_add,_root_.map_smul];
     rw [crossed s X hx v (a,a) he]; -- wrong order
     unfold crossH; rw [← monoV X hx]; simp only[s,flood, Submodule.coe_add,Submodule.coe_smul,AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,Pi.add_apply,Pi.smul_apply,_root_.map_add,_root_.map_smul,_root_.map_sum,W_sun,amt,spinStressUnsymm, _root_.map_sub,epi_at,if_pos rfl,meansE X hx,fun f p q M=> meansS X hx f p q M,sub_zero,add_zero,smul_zero,sum_const_zero]; rw [if_pos trivial,meansE X hx]; rw[gauge_val]; simp only[UV.gaugeStress, ← Perla.fullD,Submodule.coe_sub,Submodule.coe_smul, Pi.sub_apply,Pi.smul_apply,if_pos rfl,↓reduceIte,AddSubmonoidClass.coe_finsetSum,_root_.map_sum,_root_.map_sub,_root_.map_smul, fun a b i l=> meansP a b i l X hx,sum_const_zero, smul_zero,sub_zero,zero_add]; exact mul_one z -- maybe

omit hx
variable (σ:RawSym)
def RightAuth(σ:RawSym):Prop:= ∀ (d:ℕ)(t:Label d), projection (σ.adj d timeAxis t)=0 → projection t=0
include σ
local notation "Dx"=>points (![0,(1:ℝ) • basis timeAxis])
local notation "Dh"=> show Dx∈conf 2 from DawnS.distinct 1 zero_lt_one
lemma shutD {d:ℕ}(x:Label d)(s:RightAuth σ)(h:∀ y:Label d,dual d d Dx x.val y.val=0): projection x=0:=by
     let t:=σ.adj d timeAxis x; apply s d x; change projection t=0; by_contra hp; have hT:= DawnS.detecting 1 zero_lt_one t σ hp; let p:=σ.adj d timeAxis t; have he:p=x:=Subtype.ext (by unfold p t; rw [σ.adjActs,σ.adjActs]; exact UV.eyeTwist timeAxis x.val)
     rw [show σ.adj _ _ t=x from he] at hT; exact hT.ne' ((wellness Dx x t).symm.trans (h t))
lemma wayZ (s:RightAuth σ)(p:Fin 4→ℂ)(r:Values 4)(h:∀(i:Axis)(q:Label 10), gale (d:=10) Dx Dh (poseσ (r,p)) i q.val= 0): H (poseσ (r,p))=shore (p 1) (fun i=>4*r i 1)+ p 0 • H epi:=by
     apply reachZ; funext i; apply shutD σ _ s; intro q; have hg:= h i q; rw [pollen] at hg; exact hg
lemma cliff (s:RightAuth σ) (h:∀(i:Axis)(q:Label 10),gale (d:=10) Dx Dh v i q.val=0)(hz:crossH 0 v (0,0)=0) : ∃ (p:ℂ)(r:Flavor 6→ℂ), H v= shore p r :=by
   obtain ⟨⟨r,p⟩,rfl⟩:= bona.1.2 v; have h0:= wayZ σ s p r h; have hp:= crime 0 (poseσ (r,p)) (p 1) (p 0) (fun i=>4*r i 1) 0 (fun i j _=>Subsingleton.elim _ _) h0
   refine ⟨p 1,fun i=>4*r i 1,?_⟩; rw[←hp,hz,zero_smul,add_zero] at h0; exact h0
end YM.Hail
#print axioms YM.Hail.crime
#print axioms YM.Hail.cliff
