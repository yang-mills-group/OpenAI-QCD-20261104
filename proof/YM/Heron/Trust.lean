import YM.Heron.TrueL
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Arise.Range
open Maxwell.Free (fromCenter)
open Matrix Finset
variable {d:ℕ} (u:Flavor 6)(i j:Pinor)(a b:Hue)(p q:Multi d)(B:EuPin)(t:Bool)
variable (g h:PClan)
local notation "T"=> SpinMode d
lemma acrossL : tileT g t d * tileT h t d= tileT (h*g) t d:=by
    apply Matrix.ext; intro i j; let P:= g i.2; let Q:= h i.2; let E:=UV.turned (d:=d) P (wave (splice t P)); let Z:=UV.turned (d:=d) Q (wave (splice t Q)); rw[row_spin, show (h*g) i.2=Q*P from rfl,joint_times, ← wave_mul,← reel]; change (tileT g t d*tileT h t d) i j=(E*Z) i j; rw[Matrix.mul_apply, Matrix.mul_apply]
    apply sum_congr rfl; intro k _; rw [show tileT g t d i k= E i k from row_spin ..]; by_cases he:i.2=k.2; · rw [row_spin,←he];
    rw [show E i k=0 from (row_spin t g i k).symm.trans (un_spin t g i k he),zero_mul, zero_mul]
lemma across(v:SpinPol d) : spun h d (spun g d v) = spun (h*g) d v:=by unfold spun; rw [Grass.adapt_together,acrossL,acrossL]
lemma self_spun(v:SpinPol d):spun 1 d v=v:=by rw [show spun 1 d=_ from pictures 1 d,twist_one]
-- ColorTable.Act
variable (v:su.El)
lemma neat :Commute (tileT g false d) (colorTable (d:=d) v):=by
    let T':=tileT g false d; let C:=colorTable (d:=d) v; change T'*C=C*T'; apply Matrix.ext; intro i j; let F:=g i.2; let M:= UV.turned (d:=d) F (wave (splice false F)); have hh:M*C=C*M:=by
         unfold M C; rw [UV.groom,reel,reel]; simp only [mul_one,one_mul]; rw [(_root_.YM.QCD.Lat.interlace ..).eq] -- direction
    rw[show (T'*C) i j= (M*C) i j from (by rw[Matrix.mul_apply,Matrix.mul_apply]; exact sum_congr rfl fun k _=>congr_arg (· * C k j) (row_spin false g i k)), hh]; unfold C; rw [UV.groom,Matrix.mul_apply,Matrix.mul_apply]; refine sum_congr rfl fun k _=>?_ ; by_cases he:i.2=k.2; · apply congr_arg; change M k j=tileT g false d k j; rw[row_spin,← he]
    simp only[UV.turned, Matrix.of_apply, he, if_false,zero_mul]
lemma toast : Commute (tileT g true d) ((star (colorTable (d:=d) v)).transpose):=by
    let T':=tileT g true d; let C:=(star (colorTable (d:=d) v)).transpose; change T'*C=C*T'; apply Matrix.ext; intro i j; let F:=g i.2; let M:=UV.turned (d:=d) F (wave (splice true F)); have hh:M*C=C*M:=by
        unfold M C; rw [alcohol,reel,reel]; simp only [mul_one,one_mul]; apply congr_arg; exact (inter_opp (colour v) F.matrix.val).eq.symm -- adjust orientation.S
    rw[show (T'*C) i j= (M*C) i j from (by rw[Matrix.mul_apply, Matrix.mul_apply]; exact sum_congr rfl fun k _=>congr_arg (· * C k j) (row_spin true g i k)),hh]; unfold C; rw[alcohol,Matrix.mul_apply,Matrix.mul_apply]; apply sum_congr rfl; intro k _; by_cases he:i.2=k.2; · apply congr_arg; change M k j=tileT g true d k j; rw [row_spin,← he]
    simp only[UV.turned,Matrix.of_apply,he,if_false,zero_mul]
end YM.Heron
#print axioms YM.Heron.across
#print axioms YM.Heron.toast
