import YM.Lapin.Kroft
/-! Leading probes on signal fibers. genuine costs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(u:Averaging)(T:TaperHol)
local notation "φ"=> A.density i
local notation "G"=> marque (i:=i) A false a (0:Axis)
local notation "X"=> report A G u i 0
local notation "Z"=> foil φ X
local notation "P"=> rayC φ a
local notation "V"=> wave (gamma 0)
local notation "W"=> wave (gamma 1)
local notation "Q"=>wave (gamma 0*gamma 1)
open QCD.Entr.Goals Patria.Gall.Seals
local notation "U₁"=> Rod M T.T
local notation "V₁"=> Rv T.T
local notation "O"=> (0:Multi 10)
-- local matrices real norms
noncomputable def entryH (i j:Fiber): Bundle →L[ℂ]ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun x=>x i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
local notation "j"=> ax1
local notation "j'"=> ax2
local notation "G0"=> (-(2:ℂ)*Q j j')⁻¹
lemma radiant (T W': Bundle) (η:ℝ)(hT: ‖T+W‖≤ η)(hW:‖W'-W‖≤η): ‖G0*( -(T*V) - V* W') j j'-1‖ ≤ ‖G0‖*(‖entryH j j'‖*(2*η)) :=by
        have hg : G0* ((-(2:ℂ)) • Q) j j'=1:=by change G0* (-(2:ℂ)*Q j j')=1; exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) Plans.Stamp.Stair.wind_h.choose_spec.choose_spec)
        have hh: (-(2:ℂ)) • Q= W* V - V*W :=by
            rw [wave_mul,wave_mul,QCD.Lat.clifford (show (1:Axis)≠0 from by decide),QCD.Revolve.wave_neg,neg_smul,two_smul]; abel -- two_mul wrong
        let D:= (-(T*V)- V*W')-((-(2:ℂ)) • Q); have hV: ‖V‖=1:=primeU _ (W_unit _ ⟨by simp,by simp⟩)
        have he:‖D‖ ≤2*η:=by
             rw [show D= -((T+W)*V+ V*(W'-W)) from (by unfold D; rw[hh,add_mul,mul_sub]; abel), norm_neg]; apply (norm_add_le ..).trans; apply (add_le_add (norm_mul_le ..) (norm_mul_le ..)).trans; rw[hV,mul_one,one_mul,two_mul]; exact add_le_add hT hW
        rw [show G0*_ -1= G0* entryH j j' D from (?_ : G0 *( (-(T*V)- V* W') j j')-1= G0 *entryH j j' D), norm_mul]; exact mul_le_mul_of_nonneg_left (((entryH j j').le_opNorm D).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))) (norm_nonneg _)
        change _= G0*(D j j'); unfold D; rw [Matrix.sub_apply (-(T*V)- _), mul_sub, hg]
noncomputable def bail1:ℝ:= ‖G0‖*‖entryH j j'‖*2
lemma bail1_nn : 0 ≤ bail1:=by unfold bail1; positivity
variable (y:RawVec 10) (η:ℝ)
include hA hi
lemma κ_P (hY:Tally T 0 (y.val 0) φ X) (hV:Globe.Tempo P)(hp:‖U₁ 0 P-V‖≤η): ‖pay1 (lookB y) - Pi.single a 1‖≤ bail1*η:=by
        have ht:‖U₁ 1 P-W‖≤η:= Oriole.lit P 0 1 T.T hV η hp; have hz:= paid_j P 1 T.T hV η ht; have hη:0 ≤ η:=(norm_nonneg _).trans ht; apply (pi_norm_le_iff_of_nonneg (mul_nonneg bail1_nn hη)).mpr; intro b; change ‖G0*point1 1 b j j' (y.val 0)- _‖≤ _; rw [ingot A hA hi a b 0 1 u T (y.val 0) hY j j']; split
        next h=>rw [h]; rw[Pi.single_eq_same]; apply (radiant _ _ η hz ht).trans_eq; unfold bail1; ring
        next h=> rw [Pi.single_eq_of_ne h]; simp only [mul_zero,sub_self,norm_zero]; positivity[bail1_nn]
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.κ_P
