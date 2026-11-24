import YM.Eole.Heart
import YM.Pollen.Bakes
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
variable {K₁:Type} (Ku:Rail c 6 K₁)
local notation "mT"=> ample 6 J
local notation "F'"=> feather W g Y q o p old a f z h
local notation "Z0"=> hats W g Y
local notation "WZ"=> Stretch.Basin (feather W g Y q o p old a f z h) (hats W g Y) P.threshold
variable (hp_root:∀ (j:Rootπ W g),a (.inr j.val)=(Y j.val).place)(he:(tails W g Y q o p old a f z h).Reg P.threshold)(ht:Correspond (faultK 6 p t (tails W g Y q o p old a f z h)) Ku)
local notation "S"=> sachet W g Y q old a f P
open QCD.Jets QCD.Jets.Touch
local notation "XE"=> lucida W g Y q o p old a f z h
local notation "V"=> Cape.vesta p (S) t
variable {ν τ θ κ0 π C:ℝ}(L1:Side)(x:ℝ)
local notation "T1"=> taxK L1 x (39/20)
local notation "T2"=> taxK L1 x (37/20)
local notation "T3"=> taxK L1 x (9/5)
local notation "αL"=> (25/256:ℝ)
local notation "bS"=> (1/256:ℝ)
local notation "αR"=>(αL+bS)
local notation "αH"=>(21/256:ℝ)
local notation "αk"=>(18/256:ℝ)
local notation "qz"=>(1/2:ℝ)
local notation "ε"=>(2/256:ℝ)
open Push.AbsoluteSums.Trees
local notation "B1"=> ν*(1-qz)⁻¹
local notation "Bz"=>rentM P.B P.order P.power bS*B1
variable (hh:Ready a P.B (QCD.GasP.taxed (swatch Y) (heightE P.order z) (taxK L1 x (39/20))) (26/256) ν (2/256) (1/2))(hQ: degreePrice P.B (ν*(1-(1/2:ℝ))⁻¹) (5/256) ≤1/2)(hB0:(ν*(1-(1/2:ℝ))⁻¹)*(1-(1/2:ℝ))⁻¹≤ 1) (hT:1 ≤t)
local notation "Ψ"=>taxed (swatch (E:=E) Y) z T1
include hh hT
lemma wealthF : Ready a P.B (QCD.GasP.taxed (swatch Y) z (taxK L1 x (39/20))) (αL+bS) ν ε qz:=by
     let Aμ:= swatch (E:=E) Y; obtain ⟨h1,h2,h3,h4,h5,h6⟩:= hh; rw [show αR=(26/256:ℝ) by norm_num]; have hp:=positiveZ W g Y q o p old a f z h (zero_lt_one.trans_le hT)
     have hZ(i):0 ≤ Ψ i:=mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (hp _); refine ⟨h1,h2,h3,h4,hZ,fun j=>budget_mono (h6 j) (fun i=>ite_nonneg (mul_nonneg (hZ _) (Real.exp_pos _).le) le_rfl) fun i=> ?_⟩; split; next h=> exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hp _) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))) (pow_nonneg (Real.exp_pos _).le _)) (Real.exp_pos _).le
     exact le_rfl
open Jets
variable (hwX:P.B=highR L1 x) -- inspect
variable (htW:Basal.BakeD L1 x)
local notation "U1"=>withdraw 6 p t
local notation "Y★"=> Trail V WZ T
include hp_root he ht hQ hB0 hwX htW
lemma handshake [Countable E][Countable K] (hpZ:Bz ≤ C) : ∃ (D' E':Type)(_ : Countable D')(_ :Countable E')(R: Reel c 6 J D')(Fp: Patron.Rail c (ample 6 J) E'), R.Occupant p (W.flag q) t P 2 (25/256) C (fun _=>1) ∧ Wage.Tip 6 p (W.flag q) Fp P t (18/256) (taxK L1 x (9/5)) ∧Correspond (faultK 6 p t Fp) Ku ∧ ∀ (X':Grid c)(Z': EvenA c 6), Summable (fun i:E⊕K=> ‖night old f T X' i‖)→
     NormedSpace.exp (rootR (Spine J) _ Z'+Reel.rope R T X')*withdraw 6 p t (heartK Fp T X')=Bloc.sparC κ q W (NormedSpace.exp (rootR (Spine I) κ Z'+∑' i,night old f T X' (Sum.inl i))* (∑' i,gift (night old f T X' ∘ Sum.inr) Y (flags T X') i)):=by
    have hσ:= wealthF W g Y q o p old a f z h L1 x hh hT; have hΔ:= Basal.BakeD.leg htW; rw [← hwX] at hΔ; have hθ(t:ℝ)(ha:0≤t):1≤ taxK L1 x t:=Real.one_le_exp (mul_nonneg ha (fan_pos ..).le); have hT1:1≤ T1:=hθ _ (by norm_num); have hT2:1≤ T2:=hθ _ (by norm_num); have hHv:=zero_lt_one.trans_le hT
    have hP: Wage.Tip 6 p (W.flag q) (WZ) P t αH T1:= journey W g Y q o p old a f z h hT hT1 hσ (by norm_num) (by norm_num) («ε»:=(5/256:ℝ)) (by norm_num) (by norm_num) (mul_pos hh.1 (inv_pos.mpr (by norm_num))) (show qz < 1 from by norm_num) hQ hB0
    let v:=W.flag q; have hC:= retains W g Y q o p old a f z h hT hp_root Ku he ht fun U=> prints _ U hP.tilt.uses hP.tilt.sold hT1 (by norm_num) hT
    have hVK:=stock W g Y q o p old a f z h
    let f1:=S -- rename
    have hx :Wax V T P.B (22/256) 1 t:= wax_post _ (softly W g Y q o p old a f z h hT1 hσ (by norm_num) hHv) (by norm_num) (by rw [show ν*(1- qz)⁻¹=B1 from rfl]; exact le_trans (le_mul_of_one_le_right (mul_nonneg hh.1.le (inv_pos.mpr (by norm_num)).le) (by norm_num : 1≤(1-qz)⁻¹)) hB0)
    have hE(i:L)(x:Grid c):Mint 6 p t v (f1.f i) ((V).mean i x):= Mint.initiate _ hHv _ (hVK.shades ..).1
    have hY :∀ i,shadeG ((V).mean i):=fun i X g=> congr_arg Subtype.val ((Cupola.across 6 p t v _ g _ (hVK.shades ..).1).symm.trans (congr_arg _ (hVK.paint ..)))
    have hw := Card.tipped 6 p v t V WZ hP hx hY (fun i X=> (hE ..).launch) hΔ hHv
    let Yz:= Y★; haveI : Countable L:=by unfold Cand; infer_instance -- tactic insert
    haveI : Countable (Stretch.Quants (F') (hats W g Y)):=by unfold Stretch.Quants Hard; infer_instance
    have hy':= Card.contract 6 p v t V WZ hP hx hY (fun i X=> (hE ..).launch) Ku hΔ (fun i X=> Stags.lifter 6 p v t _ (hVK.enough i) _ (hE i X)) hT hT1 hT2 (by norm_num) hC
    have hΩ:= lifeE W g Y q o p old a f z h hT1 hHv (show Ready _ _ _ αR ν ε qz from (by rw [show αR= (26/256:ℝ) by norm_num]; exact hh)) (show 0 ≤ αL from by norm_num) (show 0 < bS from by norm_num)
    refine ⟨_,_,inferInstance,QCD.Acre.Rails.glazeP .., XE,Yz,occup _ _ _ hΩ le_rfl hpZ, ?_,hy',fun Xz Zy hź=> ?_⟩ -- locale tax
    · exact ⟨⟨hw.tilt.uses,hw.tilt.pigment,Kites.tide _ hw.tilt.sold (Real.exp_pos _).le (Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num:(9/5:ℝ) ≤37/20) (fan_pos ..).le))⟩,hw.fits⟩
    let Zt:= rootR (Spine I) κ; let g':=rootR (Spine J) κ; rw [show heartK Yz T Xz=_ from extraDuty 6 p v t V WZ hP hx hT hT1 (by norm_num) (by norm_num) Xz,map_mul (U1),NormedSpace.map_exp (U1) (U1).toLinearMap.toContinuousLinearMap.continuous,show NormedSpace.exp (rootR (Spine I) κ Zy+(∑' i:E, night old f T Xz (Sum.inl i)))=_ from NormedSpace.exp_add, ← NormedSpace.map_exp (rootR (Spine I) κ) (Zt).toLinearMap.toContinuousLinearMap.continuous, mul_assoc ((rootR (Spine I) κ) (NormedSpace.exp Zy)), rescale W g Y q o p old a f z h hT hT1 hσ (by norm_num) _ hΩ (by norm_num) (NormedSpace.exp Zy) hź]; rw [NormedSpace.map_exp (rootR (Spine J) κ) g'.toLinearMap.toContinuousLinearMap.continuous, NormedSpace.exp_add,NormedSpace.exp_add]; ring
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.handshake
