import YM.Kai.BrightP
import YM.Kai.Laces
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {u t a D C v e s:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)
local notation "S★" i:arg=> S.side R i
variable (Q:Cover→Insertion (S.side R i) 6)(b:Cover)
local notation "φ"=> A.density l
lemma entireS (Ω:Averaging)(h:∀ b:Cover,SungP (Q b))(ht:l ≤ i): SungP (report A Q Ω l b):=by
    let q:= visitor S i l Ω b Q; have hv:Lat.Invariant q:=by
          intro k; ext1 x; let c:= S.side R i; let X:= Insertion c 6; let V: X→ₗ[ℝ] Lat.Fields c 6:= ((slots 6 k).toLinearMap.comp (ContinuousMap.evalCLM ℂ (Lattice.gauge k x)).toLinearMap).restrictScalars ℝ
          let U: X→ₗ[ℝ] Lat.Fields c 6:= (ContinuousMap.evalCLM ℝ x).toLinearMap; change V q= U q
          have he(x):V (Q x)=U (Q x):= h x _ _
          unfold q visitor; rw [roles,rollLinear,rollLinear, funext he]
    exact fun k U=> DFunLike.congr_fun (S.transport_gauge R A.β A.w q hv ht k) U
include hA
lemma dSung (hi:l ≤ N): SungP φ:=by rw [pier A hA hi]; exact fun k U=> DFunLike.congr_fun (S.transport_gauge R A.β A.w _ A.regulator.invariant hi k) U
open Massive.PCAC.Oren
lemma inkS (Q:Slate)(b:Cover)(hi:i≤N): SungP (inkC Q A (i:=i) b):=by
     let X:=actor A i; have hv:SungP (⇑X):=by rw[show (⇑X:Density _ 6)= _ from act A hA hi]; exact dSung A hA hi
     let o:=wrap (S★ i) b; let D:= Wagon Q o; intro k U
     obtain ⟨C,_,H⟩:= honest 6 2
     let h:BudgetPoint:=⟨2,6,1,2,1,le_rfl,le_rfl,by norm_num, by omega, by norm_num,le_rfl⟩
     change slots 6 k (D (Lattice.gauge k U) _)=D U _; rw[←show D U (slots 6 k _) =_ from (H h Q (show h.order ≤ 6 from le_rfl) (show h.power ≤ 2 from le_rfl) (S★ i) o).gauge U k (X (Lattice.gauge k U))]; exact congr_arg (D U) (hv k U)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.inkS
#print axioms YM.Massive.Patria.Gall.entireS
