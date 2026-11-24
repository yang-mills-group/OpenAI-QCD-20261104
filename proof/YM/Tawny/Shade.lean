import YM.Tawny.Dree
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Dream
open TableT Carnal Rays Perla Zinc
local notation "Y"=> Multi 10
local notation "Q"=>Label 10
local notation "P"=> projection
local notation "D"=> reduceEq
local notation "U"=>(0:Multi 10)
local notation "L"=> leadR
local notation "E"=> ηR
variable (i j k:Axis) (M:Spike)
private lemma cancel {X : Type*}[AddCommGroup X][Module ℂ X](f:Axis→Axis→X) (F:Axis→X) (hz:∀ i j,i≠j→ f i j= - f j i)(h:∀ i,f i i=F i) :∑ i:Axis,∑ j:Axis,f i j= ∑ i:Axis,F i:=by
   simp only [Fin.sum_univ_four, h]; rw [hz 1 0 (by decide),hz 2 0 (by decide),hz 3 0 (by decide),hz 2 1 (by decide),hz 3 1 (by decide),hz 3 2 (by decide)]; abel
local notation "S"=>SpinMode 10
lemma dualK : reduceEq (∑ i:Axis, bilinear a a M U (E i i))=0:=by
     let f(i j:Axis): Pol 10:=bilinear a a (M*gamma i*gamma j) U (E i j)
     have hz(i:Axis):reduceEq (∑ j:Axis,f i j)=0:= Quot.c_loss a a (L i) U (E i) (fun j=>add_next ..) _
     have hD: (∑ i:Axis,∑ j:Axis,f i j)=∑ i:Axis,bilinear a a M U (E i i):=by
           apply cancel; intro i j h; unfold f; rw[mul_assoc, mul_assoc,clifford h, mul_neg,H_swap i j,← neg_one_smul ℂ (M*_ :Spike), nourish]; exact neg_one_smul ℂ (bilinear _ _ _ _ _)
           intro i; unfold f; rw[mul_assoc,Lat.gamma_sq,mul_one]
     rw[← hD,map_sum]; simp_rw[hz,sum_const_zero]
lemma rightK :reduceEq (∑ i:Axis, bilinear a a M (E i i) U)=0:=by
     let f(i j:Axis):Pol 10:=bilinear a a (gamma j*(gamma i*M)) (E i j) U; have hz(i:Axis):reduceEq (∑ j:Axis,f i j)=0:= Quot.b_loss a a (L i) U (E i) (fun j=>add_next ..) _
     have hD:(∑ i:Axis,∑ j:Axis,f i j)=∑ i:Axis,bilinear a a M (E i i) U:=by
           apply cancel; intro i j h; unfold f; rw[← mul_assoc,← mul_assoc,clifford h.symm,neg_mul,H_swap i j,← neg_one_smul ℂ (_*M:Spike),nourish]; exact neg_one_smul ℂ (bilinear a a (gamma i*gamma j*M) _ U)
           intro i; unfold f; rw [←mul_assoc,Lat.gamma_sq,one_mul]
     rw [← hD,map_sum]; simp_rw[hz,sum_const_zero]
lemma tLocus : P ((lapL a).val i)=0:=by
     rw[lap_val]; apply Subtype.ext; change reduceEq ((∑ j:Axis,shell0 a i j):Label 10).val=0; rw [AddSubmonoidClass.coe_finsetSum]; simp_rw [shell0,basil_pond,sum_sub_distrib,map_sub,rightK, dualK,sub_zero]
lemma tOmega : P (eulerV.val i)=0:=by
     rw [oeul]; apply Subtype.ext; change reduceEq ((∑ j:Axis,∑ k:Axis,GE i j k k j): Label 10).val=0; rw [show ((∑ j:Axis,∑ k:Axis,GE i j k k j): Label 10).val=plain _ (StressFlux.eom su i).val from ?_,plainP, reduceEq, TensorProduct.map_tmul]; rw[show Maxwell.reduceEq.toLinearMap _=0 from ?_,TensorProduct.zero_tmul];
     · exact StressFlux.eom_null i
     simp_rw [StressFlux.eom,AddSubmonoidClass.coe_finsetSum,map_sum]; rfl
end Dream
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Dream.tOmega
#print axioms YM.Massive.Tawny.Cast.Dream.tLocus
