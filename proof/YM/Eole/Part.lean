import YM.Eole.Stars
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
local notation "M"=> Hearts o F
set_option quotPrecheck false
local notation "V"=> withdraw 6 o t
local notation "X"=>sparkF q o F
local notation "Y"=>hatsF o F
local notation "A"=>mark o F
variable (h: Wage.Tip 6 o q F U t b w) (ht:1 ≤ t)
include h ht
local notation "C"=>scaler m W
local notation "Pk"=>fullK q o F W
local notation "R"=> (C).comp V
variable (hp:0 ≤ b)(hw:1 ≤ w)
-- publication group by Hat.Tensor
include hp hw
lemma exact_bill (x:Grid c)(hz: Summable fun i:M=> ‖fullK q o F W i t x‖) : C (V (heartK F U.threshold x))=∑' i,gift (fun j:M=>fullK q o F W j t x) (hatsF o F) (flags U.threshold x) i:=by
     let p(i:M):= Pk i t x; let f i:= F.warp i x; let v:= R; let w:=flags U.threshold x; have he : Summable (fun i=>‖f i‖):=Ruby.income _ _ ht hw h.tilt.sold hp
     have hF:∑' i,tK F U.threshold x i= ∑' i,Plate.roof F.addr f w i:=tsum_congr fun i=>termsK ..
     let r i:=v (f i); have hR : Summable fun i=> ‖r i‖:=Film.payable v.toLinearMap.toContinuousLinearMap he
     have hh : coin F.addr r=coin (hatsF o F) p:=funext fun i=>by
              rw [fingerprint,fingerprint]; let z j:= if hatsF o F j=i then p j else 0; have hZ: Summable z:=Film.aloneC _ i p hz; rw [hZ.tsum_sigma]; exact tsum_congr fun j=> by
                    by_cases hb:F.addr j=i; · rw[tsum_fintype,if_pos hb]; simp_rw [show ∀ (k:↥(birth o F j)),z (⟨j,k⟩:M)= p (⟨j,k⟩:M) from fun k=> if_pos hb]; exact luminous q o F W h ht j x -- if z syntactic?
                    rw [tsum_fintype,if_neg hb,sum_eq_zero]; intro k hk; exact if_neg hb
     change v (heartK F U.threshold x)=_; unfold heartK; rw [hF,Film.stamps F.addr f w v he,show v ∘ f=r from rfl,catalogue _ _ _ hR,hh,← catalogue _ _ _ hz]; apply tsum_congr; intro i; unfold Plate.roof Arm gift; rw[eq_comm (b:=w)]; unfold w; congr 1
-- scale mask equality. 
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.exact_bill
