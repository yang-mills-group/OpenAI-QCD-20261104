import YM.Roan.Val
import YM.Kwick.FeeB
import YM.Roan.Rule
import YM.Clink.Brass
import YM.Kwick.Vale
import YM.Roan.Ode
import YM.Lapin.Spark
/-! End read at reference upper Hop boot.Several charts transfer.X near arbitrary.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Pane Tawny.BendR
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
local notation "g"=>Gpick
open Seals
variable (T:ℕ→Side)(hT:Tendsto (fun i => ((T i).val:ℝ)) atTop atTop)
variable (A K E W Q h s:ℝ)(P P':TaperHol)
noncomputable abbrev rainB (s:Side):ℂ:= (Gall.helm s)⁻¹ * (slope s 1 0 0-slope s 0 0 0)
include hT
lemma life_stamp : Tendsto (fun i:ℕ=> Élong (T i) A W E Q (s/((T i).val:ℝ)+h) (rainB (T i))) atTop (𝓝 (gain2*h)):=by
          let Z i:=T i; let y:=fun i=> rainB (Z i); have hp:Tendsto y atTop (𝓝 1):= polar_clock 0 T hT
          have ht:Tendsto (fun i=>( ((Z i).val:ℝ))⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp hT; have hv: Tendsto (fun i:ℕ=> tick (Z i)) atTop (𝓝 0):= Tendsto.const_div_atTop hT _; have hT': Tendsto (fun i:ℕ=> s/((T i).val:ℝ)+h) atTop (𝓝 h):=by simpa only[zero_add] using ((Tendsto.const_div_atTop hT s).add_const h)
          have hu:Tendsto (fun i:ℕ=> ‖y i-1‖) atTop (𝓝 0):= (by simpa only[sub_self,norm_zero] using (hp.sub_const 1).norm); have h':Tendsto (fun i:ℕ=>‖y i‖) atTop (𝓝 1):=by simpa only[norm_one] using hp.norm
          let H:= ‖((Zinc.whirl g (gamma 1)) aux1 aux2)⁻¹‖
          unfold Élong; have hx:= ((h'.mul (hT'.const_mul gain2)).add hu).add ((((ht.mul_const Q).mul_const A).const_mul H).add ((h'.const_mul H).mul ((((hv.add ht).mul_const E).mul_const W).const_mul eW))); exact (by simpa only [one_mul,add_zero,zero_add,mul_zero,zero_mul] using hx)
lemma bail_s : Tendsto (fun i:ℕ=> bail1*(s/ ((T i).val:ℝ)+h)) atTop (𝓝 (bail1*h)):= by simpa only [zero_add] using (((Tendsto.const_div_atTop hT s).add_const h).const_mul bail1)
local notation "κ"=> (-(2:ℂ)*wave (gamma (0:Axis)*gamma 1) ax1 ax2)
lemma dimA : Tendsto (fun i=>taxP (T i) W) atTop (𝓝 0):=by unfold taxP; simpa only [tick,mul_zero,zero_mul] using ((((Tendsto.const_div_atTop hT (2*Real.pi)).const_mul (costQ 2)).mul_const W).const_mul ‖κ⁻¹‖)
lemma dimB : Tendsto (fun i=>billR Q (T i) W) atTop (𝓝 0):=by unfold billR; simpa only[Function.comp_apply,mul_zero,zero_mul] using ((((tendsto_inv_atTop_zero.comp hT).mul_const Q).mul_const W).const_mul ‖((Zinc.whirl g (gamma 1)) aux1 aux2)⁻¹‖)
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.life_stamp
#print axioms YM.Massive.Patria.Gall.Cahoots.dimA
#print axioms YM.Massive.Patria.Gall.Cahoots.dimB
