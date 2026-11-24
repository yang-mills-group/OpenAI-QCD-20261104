import YM.Iceberg.Pitch
set_option maxHeartbeats 560000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
variable {d:ℕ}(B:EuPin)(K:Ortho)(u:Labels.Taylor su 0)(a b i j:Axis)
lemma orb_basis : Ortho.move K (basis a)=∑ i:Axis, K.val i a • (basis i):=by
       ext1 l; change M4.move K.val (basis a) _= _; rw[M4.move_basis]; simp
private noncomputable def valP (u:Labels.Taylor su 0)(a:Axis) : E4 →ₗ[ℝ]su.Color:=( (continuousMultilinearCurryFin1 ℝ E4 su.Color) (u.val a)).toLinearMap -- name
lemma valV (p:E4) : valP u a p=u.value a p:=by
    change u.val a _= u.val a _; apply congr_arg; funext i; fin_cases i; rfl
lemma curlS(K:Ortho): curl0 a b (Labels.Taylor.turn K⁻¹ u) = ∑ i:Axis,∑ j:Axis,(K.val i a*K.val j b) • curl0 i j u:=by
     have hx(i j:Axis) : (K⁻¹).val i j=K.val j i:=rfl
     rw[StressFlux.curl0_value,Labels.Taylor.turn_value,Labels.Taylor.turn_value]; simp_rw [hx,inv_inv,orb_basis, StressFlux.curl0_value, smul_sub, sum_sub_distrib, ← valV u]; simp only [map_sum, smul_sum, smul_smul]; apply congr_arg₂ (·-·); rw[sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw[map_smul,smul_smul,mul_comm]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rw[map_smul,smul_smul]
-- curvature pair transforms
lemma twiceL : Labels.rotated K (pair su i j a b).val= ∑ h:Axis,∑ l:Axis, ∑ c:Axis,∑ m:Axis, ((↑(K.val h i*K.val l j*(K.val c a*K.val m b)):ℂ)) • (pair su h l c m).val:=by
    apply Labels.eval_ext; intro J; unfold Labels.rotated; rw[Labels.eval_changed,StressFlux.pair_value]; simp_rw[_root_.map_sum,map_smul,StressFlux.pair_value]; change (↑(inner ℝ (curl0 i j (Labels.Taylor.turn K⁻¹ (J 0))) (curl0 a b (Labels.Taylor.turn K⁻¹ (J 0)))):ℂ)= _; rw[curlS,curlS]; simp only[sum_inner,real_inner_smul_left]; simp only [inner_sum, real_inner_smul_right,Complex.ofReal_sum,Finset.mul_sum]; simp only[Complex.ofReal_mul,smul_eq_mul,Complex.ofReal_sum]; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; ring
variable (p:PClan)
local notation "Υ"=> (B,p)
lemma putG : putH (B,p) 8 (GG i j a b)=∑ h:Axis,∑ l:Axis, ∑ c:Axis,∑ m:Axis, ((↑(B.coord.val h i*B.coord.val l j*(B.coord.val c a*B.coord.val m b)):ℂ)) • (GG h l c m):=by
    apply Subtype.ext; simp only [Submodule.coe_smul,AddSubmonoidClass.coe_finsetSum]
    change carr (B,p) _ ((pair su i j a b).val⊗ₜ[ℂ] 1)=_; rw[carr,TensorProduct.map_tmul]; simp_rw [AlgHom.toLinearMap_apply]; rw [_root_.map_one,twiceL]; rw[← Perla.plainP]; simp_rw [map_sum]; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; rw [map_smul]; rfl
variable (f:Flavor 6)(M:Spike)
local notation "U"=> (0:Multi 10)
-- general stencil reading via actual Gauge turns
lemma view (P:Labels.Jet su)(v:Pol d): Poised.Display.ready d P (carr (B,p) d v)= spun p d (Poised.Display.ready _ (Labels.changedJet (fun i=> Labels.Taylor.turn B.coord⁻¹) P) v):=by
    induction v using TensorProduct.induction_on with
    | zero=> simp
    | add x y hx hy=> simp [hx,hy]
    | tmul x y=> rw [carr,TensorProduct.map_tmul, Poised.Display.ready_t, Poised.Display.ready_t, map_smul]; change Labels.read P (Labels.rotated _ x) •_ =_; unfold Labels.rotated; rw [Labels.eval_changed]; rfl
end YM.Lobo
#print axioms YM.Lobo.putG
#print axioms YM.Lobo.view
