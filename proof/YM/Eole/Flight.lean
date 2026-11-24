import YM.Eole.Revenue
import YM.Bister.Body
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
local notation "ξ"=> Stitch.Tablet.credits
variable {ν w B' Ω δ y:ℝ}
open Push.AbsoluteSums.Trees
local notation "gp"=> QCD.GasP.taxed (swatch (E:=E) Y) z w
variable (hz:Ready a P.B (QCD.GasP.taxed (swatch Y) z w) α ν b δ)
local notation "Z"=> hats W g Y
local notation "D'"=>ν*(1-δ)⁻¹
local notation "Γ"=> shore a
local notation "r'" i:arg=> ∏ j∈ (i:Finset (E⊕K)),z j
lemma freedom (i:Hard W g Y) : (Z i).place ⊆ Γ i.val:=by intro j hj; obtain ⟨k,hk,hj⟩:=mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨Sum.inr k,mem_toRight.mp hk,h.gram k hj⟩
noncomputable def feather (h:Setting W g Y q o p old a f z P t) :Patron.Rail c (ample 6 J) (Hard W g Y) := ⟨fun i=>⟨ Γ i.val, flagsOf Y i.val,(Z i).alive,(Z i).part.trans (freedom W g Y q o p old a f z h i)⟩, fun i j=> banknote 6 p t (μ i.val T j)⟩
local notation "F'"=> feather W g Y q o p old a f z h
variable (hT:0<t)
lemma stems : Stretch.Vital (F') Z T:=by
     let B:=banknote 6 p t; refine ⟨fun i=>freedom W g Y q o p old a f z h _,fun _=>rfl,fun i V X hz hq=>congr_arg B (readings W g Y q o p old a f z h _ V X hz hq),fun i=>B.toLinearMap.toContinuousLinearMap.measurable.comp (measurableU W g Y q o p old a f z h _),fun i V=> Cape.bankG p (λt) (litH W g Y q o p old a f z h _ i.2.1.2.1 V) (rays W g Y q o p old a f z h _),fun i V Gp=>?_⟩
     let x:= μ i.val T (gauge Gp V); have hp := (Cupola.across 6 p t (λt) _ Gp x (litH W g Y q o p old a f z h _ i.2.1.2.1 (gauge Gp V)|>.1)); exact congr_arg Subtype.val (hp.symm.trans (congr_arg _ (glow_hue W g Y q o p old a f z h _ V Gp))) -- shadow Gp
-- Quits&Well plus revenue
include hT
lemma coinV (j:Hard W g Y)(x:Grid c) : Mint 6 p t (W.flag q) (glowT W g j.val) ((feather W g Y q o p old a f z h).warp j x) := Mint.initiate _ hT _ (litH W g Y q o p old a f z h _ j.2.1.2.1 x).1
omit h hT W
lemma spendT {X:Mt}{s:Finset J}{q':J→Bool}(p:J→Site c)(hT:0<t)(hx:Polite q' s X) : ‖token c (ample 6 J) t (banknote 6 p t X)‖= Stitch.Tablet.credits t X:=by
     change load (fun _=>t) (light _ (banknote 6 p t X))= _; rw[withdrawCost 6 p t hT,sum_eq_single (burst q' s)]; exact (Stitch.Tablet.polite_bill _ _ hx hT).symm; intro i _ hi; rw [show pluck _ _ _=0 from hx.spectral i hi]; exact Cove.load_zero _; simp
include h hT W
lemma wages_k (i:Hard W g Y)(V:Grid c) : ‖token c (ample 6 J) t ((F').warp i V)‖ ≤ ∏ j∈i.val,z j := (spendT p hT (litH W g Y q o p old a f z h _ i.2.1.2.1 V).1).trans_le (earnings W g Y q o p old a f z h hT _ i.2.1.2.1 V)
variable (h0:0≤ α)(hv:1≤ w)
include h0 hv hz
lemma tariff : Quits (feather W g Y q o p old a f z h) P.B (ν*(1-δ)⁻¹) w α t:=by
    let Ff: G ↪ Finset N:=⟨Subtype.val,Subtype.val_injective⟩; have hx:=revenues W g Y q o p old a f z h hz h0 hv hT Ff (fun i:G=>flagsOf Y i.val) (fun _=>rfl) (fun i=> packet W g Y q o p old a f z h _ i.2.1.1)  -- shadow
    exact ⟨_,hx,fun j V=>wages_k W g Y q o p old a f z h hT j V⟩
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.tariff
#print axioms YM.MassiveQCD.Sample.Eole.stems
