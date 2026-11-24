import YM.Tawny.Poise
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace TableT
open Carnal Perla Zinc Perla.Fore
set_option linter.unusedSimpArgs false
variable (x:Fin 4→ℂ)(y:Fin 2→ℂ)(p q: Multi 8)(i j k:Axis)
local notation "Z"=> (0:Multi 8)
local notation "L"=> UV.first
set_option maxHeartbeats 400000 in
lemma railσ0 : prism0 a Z Z ((axisσ a x).val (0,0)).val= x 0 • (1:Spike):=by
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Z Z h).val= bilinear a a 1 Z Z from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
set_option maxHeartbeats 400000 in
lemma railσ1 : prism0 a Z (L 1) ((axisσ a x).val (0,1)).val= x 1 • gamma 0:=by
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Z Z h).val= bilinear a a 1 Z Z from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
set_option maxHeartbeats 400000 in
lemma railσ2 : prism0 a Z (L 1) ((axisσ a x).val (0,0)).val= x 3 • gamma 1:=by
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Z Z h).val= bilinear a a 1 Z Z from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
set_option maxHeartbeats 400000 in
lemma railσ3 : prism0 a Z (L 0) ((axisσ a x).val (0,0)).val= x 1 • (gamma 0+gamma 0) + x 2 • (gamma 0+gamma 0)+x 3 • gamma 0:=by
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Z Z h).val= bilinear a a 1 Z Z from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
set_option maxHeartbeats 400000 in
lemma railα0 : prism0 a Z (L 1) ((axisα a y).val (0,1)).val= y 0 • gamma 0:=by
     simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_arc,W_wind,trout,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Z Z h).val= bilinear a a 1 Z Z from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     simp only [true_and,sum_ite_eq,mem_univ,if_true,trio]; simp
set_option maxHeartbeats 400000 in
lemma railα1 : prism0 a Z (L 2) ((axisα a y).val (0,1)).val= y 1 • trio 2 0 1:=by
     simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_arc,W_wind,trout,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Z Z h).val= bilinear a a 1 Z Z from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     simp only [true_and,sum_ite_eq,mem_univ,if_true]
end TableT
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.TableT.railα0
