import YM.Bwana.Peak
import YM.Creno.Kuna
/- costs bound template. T loans computed with allowance.Clays -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Kuna
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
-- formula for sufficient T. X = target sign, t at joint birth multiplied by S. HP etc.Power.N. copy oriented predicts. Paid at AUTH. 
variable (t a b g C U v P E:ℝ) -- C salary i. U=young*salary(i+1), P=puncture, E=T
noncomputable def pocket (C U v P E:ℝ):= 1+2*(C*|v|)*P*E/U^2
local notation "Ω"=> pocket C U v P E
-- a= KG(node_i), g= W3f coefficient+gap from λ.We
noncomputable def delegate (a g C U v P E:ℝ):=(1+2*a)*pocket C U v P E+2*C*g*pocket C U v P E/U
local notation "A"=>delegate a g C U v P E
-- stand inequalities 
structure Access (Y V a g C U v P E:ℝ) :Prop where
   large : 0 < Y
   trade : |2*(C/Y*v)| *P*E ≤ U^2
   up    : 0 < V
   keeps : (1+2*a)*Y≤ V
   birth : |2*(C/V*v)| *P*E ≤ U^2
   tracks : (2*(C/V))*(g*Y) ≤ U
-- earn even redundant if (1+...) term.C relax `_barrierSeek`.
variable {C U}(ht:0<C)(hu:0<U)(hp:0<P)(he:0<E)(ha:0≤a)(hg:0 ≤ g)
include ht hu hp he
lemma withK (Z:ℝ)(h:(pocket C U v P E)≤Z): 0<Z ∧ |2*(C/Z*v)| *P*E ≤ U^2:=by
      have h_ : 0<Z:=lt_of_lt_of_le (show 0<1+_ from (by change 0< 1+2*(C*|v|)*P*E/U^2; positivity)) h; refine ⟨h_,?_⟩; rw [abs_mul,abs_of_nonneg (by norm_num:(0:ℝ)≤2),abs_mul, abs_of_nonneg (div_pos ht h_).le,div_mul_eq_mul_div,← mul_div_assoc, div_mul_eq_mul_div,div_mul_eq_mul_div]; apply (div_le_iff₀ h_).2; unfold pocket at h; exact ((div_le_iff₀ (pow_pos hu 2)).1 ((le_add_of_nonneg_left zero_le_one).trans h)).trans_eq (mul_comm ..)
include ha hg
lemma extendsV (S:ℝ) (h:delegate a g C U v P E≤ S) : Access (pocket C U v P E) S a g C U v P E:=by
      let p:=pocket C U v P E; obtain ⟨hp1,hp2⟩:= withK v P E ht hu hp he p le_rfl; have hU:p>0:=hp1; have hS:1≤1+2*a:=(by linarith); let Z:=(1+2*a)*p; have hZ:p ≤ Z:=le_mul_of_one_le_left hp1.le hS
      have htV:Z ≤ S:= le_trans (le_add_of_nonneg_right (by change 0 ≤2*C*g*p/U; positivity)) h
      have hh:= hZ.trans htV; obtain ⟨hV,hP⟩:= withK v P E ht hu hp he S hh; refine ⟨hp1,hp2,hV,htV,hP,?_⟩; rw[←mul_div_assoc,div_mul_eq_mul_div,div_le_iff₀ hV]; change _ ≤ U*S; apply le_trans _ (mul_le_mul_of_nonneg_left h hu.le); have h' :2*C*(g*p)/U ≤ delegate a g C U v P E:=by unfold delegate; rw [← mul_assoc (2*C)]; apply le_add_of_nonneg_left; exact hp1.le.trans hZ
      exact ((div_le_iff₀ hu).1 h').trans_eq (mul_comm ..)
end YM.MassiveQCD.Sample.Kuna
#print axioms YM.MassiveQCD.Sample.Kuna.extendsV
