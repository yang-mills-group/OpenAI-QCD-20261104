import YM.Pollen.Actors
import YM.Pollen.Story
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c 6→L[ℂ]Fields c 6) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Z"=>Keys c 6
open ConnectedActivityE6 Blaze King
local notation "K"=> wag
local notation "T"=>Stitch.Tablet.credits
variable {J K':Type}
open Cape
local notation "H'"=> withdraw 6 o t
local notation "Q'" X:arg=> shutter Z X
-- algebra for decks. Even raw user everywhere.
variable (x:EvenA c 6)(i:I)
noncomputable def slipU : EvenA c 6→L[ℂ] Patio (Keys c 6⊕Spine I) := (LinearMap.mulRight ℂ (echoI (Keys c 6) i)).toContinuousLinearMap.comp (rootR (Spine I) (Keys c 6)).toLinearMap.toContinuousLinearMap -- mulright sign validate
local notation "Rz"=>rootR (Spine I) (Keys c 6)
lemma medal : (slipU i x).val= stake Z (burst q {i}) x.val:= by
    change (fiber (Spine I) x.val * (echoI _ i).val) = _; rw [← quiet]; exact echoOne ..
lemma slated : Polite q {i} (slipU i x):=⟨x.val,(medal x i).symm⟩ -- inspect orientation
lemma brand : pluck Z (burst q {i}) (slipU i x)=x.val:=by change scrape Z (burst q {i}) (slipU i x).val=_; rw[medal,quid]
set_option maxHeartbeats 560000 in
lemma yolks (x:P) (y:EvenA c 6): NormedSpace.exp (slipU i y)=1+slipU i y:=by
     let z:=slipU i y; have hz:z^2=0:=(pow_two _).trans ((slated y i).nilpotent (slated y i) (by simp)); have h:= (exp_series_hasSum_exp' (𝕂:=ℂ) z).tsum_eq; rw [←h, tsum_eq_sum (s:= Finset.range 2) (fun n hn=>?_)] -- args
     swap; · have hk:2≤n:= le_of_not_gt (fun hv=> hn (mem_range.mpr hv)); rw [pow_eq_zero_of_le hk hz, smul_zero] -- syntax
     simp [Finset.sum_range_succ,z]
local notation "X*" i:arg=> shutter (Keys c 6) {i}
variable {Y: Patio (Keys c 6⊕Spine I)}
lemma dollars : shutter Z ∅ (slipU i x)=0:=by rw [stamen_h Z q _ _ _ (slated ..),if_neg (by simp)]
-- spectrum connection.OK
lemma plusU (x:P) (hx: ValidPieces (Keys c 6) q univ x): shutter Z {i} x=Cupola.pick Z q ∅ x+Cupola.pick Z q {i} x:=by
     rw [keen Z q _ _ hx]; unfold Cupola.chop Cupola.slash; rw [_root_.sum_apply]; calc
       _ = ∑ j∈ ({i}:Finset I).powerset,Cupola.pick (Keys c 6) q j x := by refine Finset.sum_congr ?_ fun _ h=>rfl; ext; simp only [mem_filter, mem_univ, true_and]; rfl
       _ = _ := by
          have hp : ({i}:Finset I).powerset = {∅,{i}}:=by rw [show ({i}:Finset I)=insert i ∅ from (by simp),powerset_insert]; simp [pair_comm]
          rw [hp]; simp
lemma borderX {x:P} (y: EvenA c 6)(h:shutter Z {i} Y=slipU i y)(hz:ValidPieces Z q univ x): pluck Z (burst q {i}) (x*NormedSpace.exp Y)= pluck Z (burst q {i}) x+ pluck Z ∅ x*y.val:=by
      let B:= X* i; let u:=slipU i y; have he: B u=u:=by unfold B; rw [stamen_h Z q _ _ _ (slated ..), if_pos (Finset.Subset.refl _)]
      have hxB:B (x*NormedSpace.exp Y)=B (x+x*u):=by rw [map_mul, NormedSpace.map_exp B B.toLinearMap.toContinuousLinearMap.continuous,h,yolks _ x y,map_add,map_mul,he,mul_add,mul_one] -- signature
      rw [phoenixC Z _ _ _ hxB _ (located q _),map_add]; apply congr_arg
      let a:=Cupola.pick Z q ∅ x; let b:=Cupola.pick Z q {i} x; have hT:B (x*u)=a*u:=by rw[map_mul,he,show B x=a+b from plusU _ _ hz,add_mul,show b*u=0 from ((show Polite q {i} b from choseTuft ..).nilpotent (slated ..) (by simp)),add_zero]
      have hh:B (x*u)= B (a*u):=by rw[hT,map_mul,he,show B a=a from (stamen_h Z q _ _ _ (choseTuft ..)).trans (if_pos (empty_subset _))]
      rw [phoenixC Z _ _ _ hh _ (located q _)]
      have hx: a.val=stake Z ∅ (pluck Z ∅ x):=by have hh:a.val=stake Z (burst q ∅) (pluck Z (burst q ∅) x):=rfl; rw [burst_absent] at hh; exact hh
      change scrape Z _ (a.val*u.val)=_; unfold u; rw [hx,medal,quiet,sticker_add,quid]
noncomputable def vaultU (X:I→Grid c→ EvenA c 6) : Grid c→ Patio (Keys c 6⊕ Spine I) :=fun x=> ∑ j:I,slipU j (X j x)
lemma vault0 (X:I→Grid c→ EvenA c 6)(u:Grid c) : shutter Z ∅ (vaultU X u)=0:=by unfold vaultU; rw [map_sum]; exact sum_eq_zero fun i _=> dollars ..
lemma vaultX (X:I→Grid c→EvenA c 6)(u:Grid c) : shutter Z {i} (vaultU X u)=slipU i (X i u):=by
    unfold vaultU; rw [map_sum,sum_eq_single i]; rotate_left
    · intro j _ he; rw [stamen_h Z q _ _ _ (slated ..), if_neg (fun hp=> he (singleton_subset_singleton.mp hp))]
    · simp
    rw [stamen_h Z q _ _ _ (slated ..), if_pos (Subset.refl _)] -- type
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.borderX
