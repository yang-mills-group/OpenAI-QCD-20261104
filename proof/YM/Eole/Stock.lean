import YM.Eole.Rent
import YM.Eole.Flight
import YM.Pollen.Solo
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
local notation "κ₀"=> ample 6 J
noncomputable def sachet (P:BudgetPoint) :Cape.Lure c 6 J (Cand W g Y):=⟨fun i=>shore a i.val,fun i x=>lunarZ W g q old f i.val P.threshold x-masked P.threshold (shore a i.val) (journal W g q f i.val) x,fun i=>glowT W g i.val⟩
local notation "S"=> sachet W g Y q old a f P
local notation "St"=> lucida W g Y q o p old a f z h
open Cape
lemma stock : Lure.On p (W.flag q) S P.threshold:=by
    refine ⟨fun i U V hZ hU=> ?_,fun i=> (measurableU W g Y q o p old a f z h i.val).sub (masked_measurable _ _ _ (measurableJ W g Y q o p old a f z h i.val)),fun i U hv hh=> hv (?_),fun i U=>?_,fun i U Gv=> ?_,fun i=> rays W g Y q o p old a f z h i.val,lightD W g Y h.ear⟩
    · exact congr_arg₂ (·-·) (readings W g Y q o p old a f z h _ U V hZ hU) (Cape.MaskR _ _ (moodU W g Y q o p old a f z h i) U V hZ hU)
    · change μ i.val T U-masked T (shore a i.val) (Jr i.val) U=0; change Healthy T (shore a i.val) U at hh; rw [masked_eq _ _ _ _ hh,lunar_day W g Y q o p old a f z h _ U hh,sub_self]
    · let V:=shore a i.val; let X:=μ i.val T U; let y:=glowT W g i.val; change Stitch.lights y V p (W.flag q) (_ - masked T V _ U); have hV:=litH W g Y q o p old a f z h _ i.2.1.2.1 U; by_cases hU:Healthy T V U; · rw [masked_eq _ _ _ _ hU, sub_eq_add_neg]; have hY:=litter W g Y q o p old a f z h _ i.2.1.2.1 U; exact ⟨hV.1.lays hY.1.minus,hV.2.plus hY.2.neg⟩
      rw [masked_ne _ _ _ _ hU,sub_zero]; exact hV
    · let V:=shore a i.val; have hx: Healthy T V (Lattice.gauge Gv U) ↔ Healthy T V U:=by unfold Healthy; rw [gauge_flags]; -- import
      change parcelColor 6 Gv J (_- masked T V (Jr i.val) _) = _ - masked T V (Jr i.val) _; rw [map_sub, glow_hue W g Y q o p old a f z h]; by_cases hP: Healthy T V U; · rw[masked_eq _ _ _ _ hP,masked_eq _ _ _ _ (hx.2 hP),glory W g Y q o p old a f z h]
      rw [masked_ne _ _ _ _ hP,masked_ne _ _ _ _ (fun ht=> hP (hx.1 ht)),map_zero]
local notation "S₀"=> Cape.vesta p S t

open Push.AbsoluteSums.Trees
variable {ν w β δ y:ℝ}(hw:1 ≤ w)(hz:Ready a P.B (QCD.GasP.taxed (swatch Y) z w) α ν b δ)(h0:0≤ α)(hT:0<t)
include hw hz h0 hT
lemma softly : Wax (Cape.vesta p (S) t) P.threshold P.B α (ν*(1-δ)⁻¹) t:=by
     let Z:L ↪ Finset N:=⟨Subtype.val,Subtype.val_injective⟩; have hY:= stock W g Y q o p old a f z h
     have hl:=revenues W g Y q o p old a f z h hz h0 hw hT Z (fun i=>∅) (fun i:L=> (empty_dim W g Y i).2.symm) (fun i=> packet W g Y q o p old a f z h i.val i.2.1.1)
     unfold QCD.GasP.taxed at hl; simp only [card_empty,pow_zero,one_mul] at hl; refine ⟨vespers _ _ _ hY,fun i:L=>∏ j∈i.val,z j,hl,fun i U=>?_⟩
     let V:= shore a i.val; let x:=(S).wick i U; rw [show ‖token c _ t ((S₀).mean i U)‖= _ from spendT p hT (hx:=hY.shades i U|>.1)] -- arg
     by_cases hp: Healthy T V U; · rw [show (S).wick i U=0 from by_contra fun h=>hY.expense i U h hp,Stitch.Tablet.credits,map_zero,Cove.load_zero]; exact prod_nonneg fun j _=>positiveZ W g Y q o p old a f z h hT _
     change Stitch.Tablet.credits t (μ i.val T U-masked T _ _ U) ≤ _; rw [masked_ne _ _ _ _ hp,sub_zero]; exact earnings W g Y q o p old a f z h hT _ i.2.1.2.1 U
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.softly
