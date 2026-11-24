import YM.Eden.Esme
import YM.Lapin.Keeper
-- whole shifted reallocation using precisely wood only (including scalar). preserve physical readings.
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast TorusPCAC.Geometry TorusPCAC.Ward Oriole
open Next.Free
open QCD.Pine
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}
open QCD.Flume
-- Redore invariant action requirements. root actual has REAL sym.O
variable (d:ℕ)(P:Plan d)(H:Train d)(m:ℝ)
-- infer `wood` arguments
noncomputable def cedar (c:Side)(V:Grid c) := wood P 0 H V+m • (1:Sheet c)
local notation "Z"=> cedar d P H m c
open TorusPCAC.Jet TorusPCAC.Spin TorusPCAC.Jet.Selector Switch AxisB
lemma alder (V:Grid c): let D:= onSpin c Cmat; let Q:= onSpin c Cmat⁻¹
     (Q* (Z (TorusPCAC.Stencil.conjGrid V))* D).transpose= Z V:=by
       intro D Q; unfold cedar; rw [Matrix.mul_add,Matrix.add_mul, Matrix.transpose_add, Eden.unrolled,mul_smul_comm, Matrix.smul_mul,Matrix.transpose_smul,Matrix.mul_one,show Q*D=1 from fee,Matrix.transpose_one]
lemma elm(V:Grid c)(s:Signed)(p:Site c)(g:Site c→ℂ)(X:Spike)(h:Glare s (0:Site c) 0 p g)(hx:Swing s X):
     let Q:=hues p s g X; Z (pull s p V)=Q* Z V* star Q :=by
       intro Q; unfold cedar; rw[spin_wood h hx, Matrix.mul_add, Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,(colour_wheel h hx).2]; rfl
lemma ash(V:Grid c)(k:Frame c): Z (gauge k V)= siteRot k* Z V*star (siteRot k):=by unfold cedar; rw [orbital,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,(siteRot_u ..).2]
lemma cedarC : Continuous (cedar d P H m c):= (verdant ..).add continuous_const -- error
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.alder
#print axioms YM.Massive.PCAC.Oren.elm
