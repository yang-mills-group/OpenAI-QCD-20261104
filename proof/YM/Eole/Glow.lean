import YM.Eole.Sol
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
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
local notation "κ"=> Keys c 6
variable (q:I→ Bool) {P:BudgetPoint} {v α b t:ℝ}
open Further.ShellBirth49.Fusing Collide
variable (o:I→Site c)(p:J→Site c)
-- E raw footprint and common extensions
local notation "M"=> Patio ((Keys c 6)⊕Spine I)
local notation "Mt"=> Patio ((Keys c 6)⊕Spine J)
local notation "λt"=>W.flag q
variable (old:E→Support c)(a:E⊕K→Support c)(f:E⊕K→ Grid c→ Patio ((Keys c 6)⊕Spine I))(z:E⊕K→ℝ)
local notation "P₀"=> Grid c
set_option quotPrecheck false
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
lemma glowing (j:E⊕K)(x:Grid c) : Stitch.lights (g j) (a j) o q (H' x j):=by
    let y:= f j x; have he : Stitch.lights (g j) (a j) o q y:=⟨(h.price j x).1,(h.price j x).2.raise (limitsMon _ _ (up_support W g Y q o p old a f z h j))⟩
    cases j with|inr j=>exact he|inl i=> by_cases hz:Healthy T (old i) x; rw[night,lunar,masked_eq _ _ _ _ hz]; exact he; rw[night,lunar, masked_ne _ _ _ _ hz]; exact ⟨polite_nil ..,clad.nil _⟩
local notation "ξ"=> Stitch.Tablet.credits
variable (hv:0<t)
include hv
lemma wages (j:E⊕K) (V:Grid c) : ξ t (H' V j) ≤ z j:=by
    cases j with
    | inr j=> exact h.borne j V
    | inl i=> obtain ⟨k,hk⟩:=h.ear i; have hp:= h.each _ _ hk; unfold night lunar; dsimp only; by_cases hV:Healthy T (old i) V; · rw[masked_eq _ _ _ _ hV]; have hP:=chartA q (g (.inl i)) _ (fun V=>(h.price _ _).1) V hV hp hv; simpa only[leftDerivs,one_pow,mul_one] using hP.paid [] (Nat.zero_le _) (by simp)
              rw [masked_ne _ _ _ _ hV,Stitch.Tablet.credits,map_zero,Cove.load_zero]; exact hp.travels
lemma positiveZ (j:E⊕K):0 ≤ z j:= (Creek.load_nn ..).trans (wages W g Y q o p old a f z h hv j 1)
local notation "lπ"=>Bloc.lane κ q W
omit hv
-- Part λ always legal.Combined tile.Author. charge even mark swapped from reverse.Ph.W.Volume.
lemma litH (i:Finset N)(he:mural W g i)(U:Grid c): Stitch.lights (glowT W g i) (shore a i) p λt (lunarZ W g q old f i T U):=by
    refine Bloc.forecast q W (glowT W g i) o p (shore a i) _ ?_; rw [show W.plant _=bins g _ from he]; refine Stitch.Tablet.candlehouse _ _ _ _ (fun i hX=>?_) ; have hx:=glowing W g Y q o p old a f z h i U; exact ⟨hx.1,hx.2.raise (limitsMon _ _ (subset_biUnion_of_mem _ hX))⟩
lemma litter (i: Finset (E⊕K))(he:mural W g i)(U:Grid c): Stitch.lights (glowT W g i) (shore a i) p (W.flag q) (journal W g q f i U):=by
    refine Bloc.forecast q W _ o p _ _ ?_; rw [show W.plant _= bins g _ from he]; refine Stitch.Tablet.candlehouse _ _ _ _ (fun i hx=> ?_) ; have hP:= h.price i U; exact ⟨hP.1,hP.2.raise (limitsMon _ _ ((up_support W g Y q o p old a f z h i).trans (subset_biUnion_of_mem _ hx)))⟩
-- color rules
lemma glow_col (i:E⊕K)(U:Grid c)(v:Frame c) : parcelColor 6 v I (H' (gauge v U) i)=H' U i:=by
    have hp(i:Support c) :Healthy T i (gauge v U) ↔ Healthy T i U:=by unfold Healthy; rw [gauge_flags]
    cases i with
    | inr i=>exact h.color _ _ _
    | inl i=> by_cases he:Healthy T (old i) U; · simp only[night,lunar,masked_eq _ _ _ _ he,masked_eq _ _ _ _ ((hp _).2 he)]; exact h.color .. -- placeholder
              rw[night, night]; dsimp only[lunar]; rw [masked_ne _ _ _ _ (fun hj=>he ((hp _).1 hj)),masked_ne _ _ _ _ he,map_zero]
lemma glow_hue(i:Finset (E⊕K))(U:Grid c)(v:Frame c) : parcelColor 6 v J (lunarZ W g q old f i T (gauge v U))=lunarZ W g q old f i T U:=by
    let s:=glowT W g i; change parcelColor _ _ _ (lπ s _) = lπ s _; rw [←Bloc.colored,map_prod]; exact congr_arg _ (prod_congr rfl fun j _=> glow_col W g Y q o p old a f z h j U v)
lemma glory (i:Finset (E⊕K)) (U:Grid c)(v:Frame c) : parcelColor 6 v J (journal W g q f i (gauge v U))= journal W g q f i U:=by
    let s:=glowT W g i; change parcelColor _ _ _ (lπ s _) = lπ s _; rw [←Bloc.colored,map_prod]; exact congr_arg _ (prod_congr rfl fun j _=> h.color j U v)
lemma moodU (i:Cand W g Y) : LocalOn (shore a i.val) (journal W g q f i.val):=by
    refine fun X V hx=> congr_arg (lπ (glowT W g i.val)) (prod_congr (f:=day f X) (g:=day f V) rfl ?_); intro j hj; cases j with
    | inl j=> exact h.mood j X V (agrees_mono hx ((h.grows _).trans (subset_biUnion_of_mem a hj)))
    | inr j=> exact (i.2.2 ⟨j,mem_toRight.mpr hj⟩).elim
lemma measurableU (i:Finset (E⊕K)): Measurable (lunarZ W g q old f i T) :=by
    apply Measurable.comp (f:=fun U=> ∏ j∈i,H' U j) (g:=lπ (glowT W g i)) (ContinuousLinearMap.measurable (lπ _)); apply Finset.measurable_fun_prod; rintro (j|j) _; exact masked_measurable _ _ _ (h.readable _); exact h.readable _
lemma measurableJ (i: Finset (E⊕K)): Measurable (journal W g q f i) :=by
    apply Measurable.comp (f:=fun U=> ∏ j∈i,f j U) (g:=lπ (glowT W g i)) (ContinuousLinearMap.measurable (lπ _)); exact Finset.measurable_fun_prod _ fun i _=> h.readable i
-- agreement on masks
lemma lunar_day (i:Finset (E⊕K))(U: Grid c)(he:Healthy T (shore a i) U): lunarZ W g q old f i T U= Jr i U:=by
    refine congr_arg (lπ (glowT W g i)) (prod_congr (f:=H' U) (g:=day f U) rfl ?_); intro j hj; cases j with | inr j=>rfl|inl j=>exact masked_eq _ _ _ _ (he.mono_left ((h.grows _).trans (subset_biUnion_of_mem _ hj)))
include hv
lemma earnings (i:Finset (E⊕K))(he:mural W g i) (U:Grid c): ξ t (lunarZ W g q old f i T U) ≤ ∏ j∈i,z j :=by
     let s:=glowT W g i; let F':= H' U; have hq:Polite q (W.plant s) (∏ j∈i,F' j):= (show W.plant _= bins g _ from he).symm ▸ paint_packets g q F' (fun i=> (glowing W g Y q o p old a f z h i _).1) i
     rw [show ξ t (μ i T U)=_ from Bloc.value_norm q W s hv _ hq]; exact Cove.funded _ _ _ _ fun i _=> wages W g Y q o p old a f z h hv i U
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.glory
