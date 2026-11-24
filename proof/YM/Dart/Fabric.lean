import YM.Needle.Stove
import YM.Dart.Book
import YM.Dart.Palm
/-!
  # Additive deterministic aperture for matching all finite sums
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) (d:ℕ)
local notation "S"=> C.S
set_option quotPrecheck false
variable {P d} {E:Hub.Invest P d}(H:Rack E)
structure Arc (H:Rack E) (x:(i:ℕ)→stalk C i) (a:ℕ→Label d):Prop where
    wealth : ∃ A:ℝ,0 < A∧ ∀ᶠ i:ℕ in atTop,H.w i (a i) ≤ A*H.κ i
    tideP : ∀ᶠ j in atTop,∃ F:ℕ→ℝ,Tendsto F atTop (𝓝 0)∧ ∀ᶠ i in atTop,0≤ F i ∧FocusK C i j (x i-stem P d i (a i)) (F i)
namespace Arc
variable {H}{x y:(i:ℕ)→stalk C i}{a b:ℕ→ Label d}(hx:Arc H x a)(hy:Arc H y b)
include hx hy
lemma together :Arc H (x+y) (a+b):=by
    constructor
    · obtain ⟨A,hA,H1⟩:=hx.wealth; obtain ⟨B,hB,H2⟩:= hy.wealth; refine ⟨A+B,add_pos hA hB,?_⟩; filter_upwards [H1,H2,H.sw] with i hi hz hp
      have h:=hp (a i) (-b i); rw [sub_neg_eq_add, ← neg_one_smul ℂ (b i), H.dimM, norm_neg,norm_one,one_mul] at h; exact h.trans ((add_le_add hi hz).trans_eq (add_mul A B _).symm)
    filter_upwards [hx.tideP, hy.tideP] with j hj hx; obtain ⟨F,hF,h⟩:=hj; obtain ⟨G,hG,hP⟩:=hx; refine ⟨fun i=> F i+G i,by simpa only [zero_add] using hF.add hG,?_⟩; filter_upwards [h,hP] with i hi hx; refine ⟨add_nonneg hi.1 hx.1,?_⟩; rw [Pi.add_apply,Pi.add_apply,map_add,add_sub_add_comm]; exact FocusK.add hi.2 hx.2
omit hx hy
lemma zero (d:ℕ)(E:Hub.Invest P d) (H:Rack E) : Arc H 0 0:=by
    have ht(i):H.w i 0=0:=by simpa only [zero_smul,norm_zero,zero_mul] using H.dimM i 0 0
    refine ⟨⟨1,zero_lt_one,Eventually.of_forall fun i=>by rw [Pi.zero_apply,ht]; exact (mul_nonneg zero_le_one (H.κ_pos _).le)⟩, Eventually.of_forall fun j=>?_ ⟩; refine ⟨fun _=>0,tendsto_const_nhds, Eventually.of_forall fun i=>?_⟩; exact ⟨le_rfl,by rw [Pi.zero_apply,Pi.zero_apply,map_zero,sub_zero]; exact FocusK.zero⟩
lemma spread {I:Type*}(s:Finset I)(X:I→(i:ℕ)→stalk C i)(v:I→ℕ→ Label d)(hp:∀ i∈s, Arc H (X i) (v i)): Arc H (∑ i∈s,X i) (∑ i∈s,v i):=by
    induction s using Finset.induction_on with |empty=>simp only [sum_empty]; exact Arc.zero _ _ _|insert a s ha ih=> rw [sum_insert ha,sum_insert ha]; exact together (hp a (mem_insert_self ..)) (ih fun i hi=>hp i (mem_insert_of_mem hi))
include hx
lemma scaled (f:ℕ→ℂ)(B:ℝ)(hB:0 <B)(hv:∀ᶠ i in atTop,‖f i‖ ≤ B):Arc H (fun i=> f i • x i) (fun i=> f i • a i):=by
    constructor
    · obtain ⟨A,hA,hF⟩:=hx.wealth; refine ⟨B*A,mul_pos hB hA,?_⟩; filter_upwards [hv,hF] with i h hp; rw [H.dimM]; exact ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans ((mul_le_mul_of_nonneg_right h (mul_nonneg hA.le (H.κ_pos _).le)).trans_eq (mul_assoc B A _).symm))
    filter_upwards [hx.tideP] with j h; obtain ⟨F,hF,h⟩:= h; refine ⟨fun i=>B*F i,by simpa only [mul_zero] using hF.const_mul B,?_⟩; filter_upwards [h,hv] with i hi hx; refine ⟨mul_nonneg hB.le hi.1,?_⟩; rw [map_smul, ← smul_sub]; exact FocusK.mono (FocusK.smul hi.2 _) (mul_le_mul_of_nonneg_right hx hi.1)
end Arc
end YM.Massive.Needle
#print axioms YM.Massive.Needle.Arc.scaled
#print axioms YM.Massive.Needle.Arc.spread
