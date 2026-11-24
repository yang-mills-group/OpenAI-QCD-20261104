import YM.Tawny.Cards
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Drill
open TableT Carnal Rays Perla Zinc Perla.Fore Dream Dream.Clove
open scoped Kronecker
variable (v:Axis→ℂ)(b' c: Hue)(i j k:Axis)(M:Spike)(f g: Pinor →ℂ)(h:SlashV v f) (X:Maxwell.TaylorTower su) (S: Spike)
local notation "Φ"=> vitality a v b' c f g h X
local notation "Ψ"=>goldF a v b' c f g h X
private lemma sesame (i:Axis): AtNext i (0:Multi 8) (UV.first i):=by
     funext j; by_cases h:i=j; subst j; rw [update_self,nectar,if_pos rfl]; rfl
     rw [update_of_ne (Ne.symm h),nectar,if_neg h]; rfl
lemma unit8: pay (UV.first i) v=v i:=by rw [cost_next v _ _ _ (sesame i),base_price,mul_one]
lemma unit10: pay (leadR i) v=v i:=by rw [cost_next v _ _ _ (add_zeroL i),base_price,mul_one]
lemma square10: pay (ηR i i) v=v i*v i:=by rw [cost_next v _ _ _ (add_next i i),unit10]
local notation "Q"=> rowC g f
local notation "P"=> UV.first
local notation "Z"=> (0:Multi 8)
include h
lemma proudA(p q: Multi 8)(hX: p≠0): Φ 8 (bilinear b b M p q)=0:=by rw [epig]; simp [hX]
lemma phaseσ : Φ 8 (alter b i j).val= if b=a ∧ b'=c then v j * rowC g f (gamma i) else 0:=by rw [amt]; unfold spinStressUnsymm; rw [map_sub, proudA a b v b' c (gamma i) f g h X _ _ (Oriole.highV j), sub_zero,epig]; simp only[unit8,and_true] -- placeholder vars
lemma dimT : Φ 8 (((traceT b).val (i,j)).val)=0:= (auditor a v b' c f g h X ((traceT b).val _).val ((Qeq _).1 (oppH ..))).1
lemma scalarR : Φ 8 (((scalarS b).val (i,i)).val) = if b=a∧b'=c then Q 1 else 0:=by
    rw [W_mass]; simp only [↓reduceIte]; change Φ _ (bilinear _ _ _ _ _)=_; rw[epig,base_price]; simp only [and_true, one_mul]
lemma polar_meter (x:Fin 4→ℂ)(he:b≠a) : Φ 8 (((axisσ b x).val (i,j)).val)=0:=by
    simp only [axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul]; rw [dimT,W_sun,W_wing]; simp only [W_sun,Submodule.coe_add,map_add,phaseσ,he,false_and,if_false]; split <;> rename_i hp -- split wing
    · subst j; rw [scalarR]; simp [he,map_add,phaseσ,W_sun]
    rw [W_mass,if_neg hp]; simp
lemma polarFog (x:Fin 4→ℂ) : Ψ 8 (((axisσ b x).val (i,j)).val)=0:=by
   simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul]; rw [W_wing,W_trace,W_mass]; split <;> simp only [W_sun,Submodule.coe_add, Submodule.coe_smul,map_add,map_sum,map_sub,AddSubmonoidClass.coe_finsetSum,amt,spinStressUnsymm, show ∀ h,(solstice b 1 Z Z h).val= bilinear b b 1 Z Z from fun _=>rfl,p_hue,sum_const_zero,Submodule.coe_zero,map_zero, sub_zero,add_zero,smul_zero]
lemma flame_A (he:b≠a) : Φ 8 (((windS b).val (i,j)).val)=0:=by rw [W_wind]; change Φ _ (_- _)= _; rw [map_sub]; simp_rw [phaseσ _ _ _ _ _ _ _ _ _ _ _]; simp [he]
lemma flame_B (he:b≠a) : Φ 8 (((arcS b).val (i,j)).val)=0:=by
     rw [W_arc,AddSubmonoidClass.coe_finsetSum]; simp_rw [map_sum,trout,map_add,epig]; simp [he]
variable (u:Values 4)(Y:Values 2)(z:Fin 4→ℂ)
lemma pricedσ : Φ 8 (((poseσ (u,z)).val (i,j)).val)=Φ 8 (((axisσ a (u a)).val (i,j)).val):=by
    change Φ _ (((poseσT u+gaugeσ z).val (i,j)).val)=_
    have hz:Φ 8 (((gaugeσ z).val (i,j)).val)=0:=by obtain ⟨hp,hs,hy,hv⟩:=meter_s a v b' c i j f g h X; simp [gaugeσ,hp,hs,hy,hv]
    simp only[Submodule.coe_add,Pi.add_apply,map_add,hz,add_zero,poseσT,AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum]; rw [sum_eq_single a]; intro b _ hh; exact polar_meter a b v b' c i j f g h X _ hh; simp
lemma moneyσ : Ψ 8 (((poseσ (u,z)).val (i,j)).val)=pages (Perla.Fore.lexY X) ((gaugeσ z).val (i,j)):=by
     change Ψ _ (((poseσT u+gaugeσ z).val (i,j)).val)=_; simp only[Submodule.coe_add,Pi.add_apply,map_add,poseσT,AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum,polarFog,sum_const_zero,zero_add]; exact shine_S ..
lemma pricedα : Φ 8 (((poseα Y).val (i,j)).val)=Φ 8 (((axisα a (Y a)).val (i,j)).val):=by
    rw [show poseα Y=∑ b:Flavor 6,axisα b (Y b) from rfl]; simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum]; rw [sum_eq_single a]; intro b _ hb; simp [axisα,flame_A a b v b' c i j f g h X hb,flame_B a b v b' c i j f g h X hb]; simp
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.pricedσ
