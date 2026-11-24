import YM.Tawny.Gyre
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
-- Generate all 6 determinant rows pay verified
namespace TableT
open Rays Carnal Perla Zinc Perla.Fore
local notation "V" => RawVec 10
local notation "U"=> (0:Multi 10)
local notation "J"=> leadR
local notation "L"=> ηR
local notation "I"=> (0:Axis)
local notation "B"=> (1:Axis)
variable (x:Fin 7→ℂ)
local notation "c" p:arg q:arg=>prism0 a p q
set_option quotPrecheck false
local notation "g" p:arg q:arg=>prism0 a p q ((vectorZ a x).val I).val
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 740000 in
lemma row0: g U (J I)= x 0 • (1:Spike) + x 1 • (1:Spike):=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_sub,bareB,show ∀ i j, (med a i j (gamma j)).val= youthL a i j (gamma j) from fun _ _=>rfl,fork,lotJ,tip,hic, hit, tap, show ∀ i j k, ηR i j≠ leadR k from fun i j k=> Ne.symm (tap k i j), fun i=> Ne.symm (hic i),fun i j=>Ne.symm (hit i j)]
    all_goals simp [Fin.sum_univ_four, Fin.ext_iff]
set_option maxHeartbeats 740000 in
lemma row1: g U (J B)= x 1 • (gamma I*gamma B):=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_sub,bareB,show ∀ i j, (med a i j (gamma j)).val= youthL a i j (gamma j) from fun _ _=>rfl,fork,lotJ,tip,hic, hit, tap, show ∀ i j k, ηR i j≠ leadR k from fun i j k=> Ne.symm (tap k i j), fun i=> Ne.symm (hic i),fun i j=>Ne.symm (hit i j)]
    all_goals simp [Fin.sum_univ_four, Fin.ext_iff]
set_option maxHeartbeats 740000 in
lemma row2: g U (L I I)=  x 2 • gamma I+x 3 • gamma I+x 4 •gamma I:=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_sub,bareB,show ∀ i j, (med a i j (gamma j)).val= youthL a i j (gamma j) from fun _ _=>rfl,fork,lotJ,tip,hic, hit, tap, show ∀ i j k, ηR i j≠ leadR k from fun i j k=> Ne.symm (tap k i j), fun i=> Ne.symm (hic i),fun i j=>Ne.symm (hit i j)]
    all_goals simp [Fin.sum_univ_four, Fin.ext_iff]
set_option maxHeartbeats 740000 in
lemma row3: g U (L B B)= x 3 • gamma I:=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_sub,bareB,show ∀ i j, (med a i j (gamma j)).val= youthL a i j (gamma j) from fun _ _=>rfl,fork,lotJ,tip,hic, hit, tap, show ∀ i j k, ηR i j≠ leadR k from fun i j k=> Ne.symm (tap k i j), fun i=> Ne.symm (hic i),fun i j=>Ne.symm (hit i j)]
    all_goals simp [Fin.sum_univ_four, Fin.ext_iff]
set_option maxHeartbeats 740000 in
lemma row4: g U (L I B)= x 4 • gamma B:=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_sub,bareB,show ∀ i j, (med a i j (gamma j)).val= youthL a i j (gamma j) from fun _ _=>rfl,fork,lotJ,tip,hic, hit, tap, show ∀ i j k, ηR i j≠ leadR k from fun i j k=> Ne.symm (tap k i j), fun i=> Ne.symm (hic i),fun i j=>Ne.symm (hit i j)]
    all_goals simp [Fin.sum_univ_four, Fin.ext_iff]
set_option maxHeartbeats 740000 in
lemma row5: g (J B) (J I)= x 5 • gamma B:=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_sub,bareB,show ∀ i j, (med a i j (gamma j)).val= youthL a i j (gamma j) from fun _ _=>rfl,fork,lotJ,tip,hic, hit, tap, show ∀ i j k, ηR i j≠ leadR k from fun i j k=> Ne.symm (tap k i j), fun i=> Ne.symm (hic i),fun i j=>Ne.symm (hit i j)]
    all_goals simp [Fin.sum_univ_four, Fin.ext_iff]
end TableT
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.TableT.row3
