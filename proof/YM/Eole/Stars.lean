import YM.Eole.Shake
import YM.Eole.Rate
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
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
namespace Gain
open QCD.GasP
local notation "m"=> Keys c 6
local notation "G"=> Grid c
local notation "P"=>Patio (m⊕Spine I)
variable {t u v x b w γ:ℝ}{U:BudgetPoint}
variable (q:I→Bool) (o:I→Site c)(F: Rail c (ample 6 I) K) (W:I→ℝ)
-- expand basis support over all physically allowed markers using F location.G
noncomputable abbrev birth (j:K):= (barn o (F.addr j).place).powerset
noncomputable abbrev Hearts (o:I→Site c)(F:Rail c (ample 6 I) K) := Sigma fun i=> ↥(birth o F i)
local notation "M"=> Hearts o F
set_option quotPrecheck false
local notation "V"=> withdraw 6 o t
noncomputable abbrev mark (j:Hearts o F):Finset I:=j.2.val
noncomputable def sparkF (j:Hearts o F)(x:Grid c)(t:ℝ):Patio ((Keys c 6)⊕Spine I):= (Cupola.pick m q (mark o F j)) (withdraw 6 o t (F.warp j.1 x))
abbrev hatsF (j:Hearts o F):= F.addr j.1
local notation "X"=>sparkF q o F
local notation "Y"=>hatsF o F
local notation "A"=>mark o F
variable (h: Wage.Tip 6 o q F U t b w) (ht:1 ≤ t)
include h ht
lemma litK (j:M)(k:G): Stitch.lights (A j) (Y j).place o q (X j k t):= ⟨ choseTuft .., fun i=> by
     change pluck m i (Cupola.pick m q (A j) (V (F.warp j.fst k)))∈ Creek.region (limits (Y j).place)
     unfold Cupola.pick; rw [many]; split; exact pennied 6 o t i _ _ (h.tilt.uses.role _ k); exact Subalgebra.zero_mem _⟩
lemma colorK (j:M)(x:G)(v:Frame c): parcelColor 6 v I (X j (Lattice.gauge v x) t)=X j x t:=by
    apply pluckVisible; intro s; unfold sparkF Cupola.pick; rw[partColor,many,many]; split; next hf=>
             have he:= h.fits j.fst (Lattice.gauge v x); let Z:=F.warp j.fst (Lattice.gauge v x); have hX : parcelColor 6 v I (V Z)= V (F.warp j.fst x):=by
                   rw [← Cupola.home 6 o t (zero_lt_one.trans_le ht) (parcelColor 6 v I (V Z))]; apply congr_arg; rw [all_color 6 o t q _ _ he.applies, show banknote 6 o t (V Z)=Z from he.spark]; exact Subtype.ext (h.tilt.pigment ..)
             exact (partColor ..).symm.trans (congr_arg (pluck m s) hX)
    next hf=>exact map_zero _
variable (hx:1≤ w)(hc:0 ≤ b)
variable (z :K→ℝ)(hZ:∀ i V', ‖token c (ample 6 I) t (F.warp i V')‖≤ z i)
local notation "ξ"=> Stitch.Tablet.credits
lemma brightK (j:M)(x:G): ξ t (X j x t) ≤ ‖token c (ample 6 I) t (F.warp j.fst x)‖:=by
    have ht' :=zero_lt_one.trans_le ht; let X':= X j x t; let s:= burst q (A j); rw [Stitch.Tablet.polite_bill (A j) X' (litK q o F h ht j x).1 ht', show scrape m s X'.val= pluck m s (V (F.warp j.fst x)) from ?_]; exact Well.pin s ht' (h.fits ..) -- arg
    change pluck m s (chooseBlade m s (V _))=_; rw[many,if_pos rfl]
lemma birth_bill (j: K)(x:Grid c) : (V) (F.warp j x)=∑ s:↥(birth o F j),sparkF q o F (⟨j,s⟩:M) x t:=by
     have he:= h.fits j x; let A':= V (F.warp j x); let g i:= Cupola.pick m q i A'; have hp : A'=∑ i,g i:=by simpa [g] using he.applies.wholeV
     change A'=∑ s:↥(birth o F j),g s.val; rw[sum_coe_sort]; apply hp.trans; symm; refine sum_subset (subset_univ _) (fun i _ hx=>?_); have ht':0 <t:=zero_lt_one.trans_le ht
     apply Subtype.ext; change stake m _ (pluck m (burst q i) A')=_; have hx': ¬burst q i⊆ limitQ o (F.addr j).place:=fun hX=>hx (mem_powerset.mpr (fun k hk=>(inside ..).2 ((held_pins ..).mp hX (mem_image_of_mem _ hk))))
     rw[show pluck _ _ _=0 from confined 6 o t _ _ _ (h.tilt.uses.role _ x) hx',map_zero]; rfl
-- scale labels globally AFTER negotiation.
local notation "C"=> scaler m W
noncomputable abbrev uvBirth (W:I→ℝ)(s: Finset I):= ∏ i∈s,(W i:ℂ)
noncomputable def fullK (j:M) (t:ℝ)(x:Grid c):= uvBirth W (A j) • sparkF q o F j x t
local notation "Pk"=> fullK q o F W
lemma luminous (j:K)(x:G): C (V (F.warp j x))= ∑ s: ↥(birth o F j), Pk (⟨j,s⟩:M) t x:=by
    rw [birth_bill q o F h ht j x,map_sum]; exact sum_congr rfl fun _ _=> stamen m q W _ _ (choseTuft ..)
lemma compactK (j:M): Measurable (fullK q o F W j t):=by
     let Y':= (Cupola.pick m q (A j)).comp (V).toLinearMap.toContinuousLinearMap
     exact (Y'.continuous.measurable.comp (h.tilt.uses.reads _)).const_smul (uvBirth W (A j))
lemma studies (j:M): UsesFinal U.threshold ((hatsF o F j).place) (fullK q o F W j t):=by
     intro i k hh hx; unfold fullK sparkF; rw [h.tilt.uses.uses _ i k hh hx]
lemma phases (j:M)(x:G)(v:Frame c): parcelColor 6 v I (Pk j t (Lattice.gauge v x))=Pk j t x:=by unfold fullK; rw [map_smul,colorK q o F h ht]
lemma candles (j:M)(x:G): Stitch.lights (A j) (Y j).place o q (Pk j t x):=by obtain ⟨hx,hh⟩:= litK q o F h ht j x; exact ⟨hx.smooch _,hh.scale _⟩
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.luminous
#print axioms YM.MassiveQCD.Sample.Eole.Gain.brightK
