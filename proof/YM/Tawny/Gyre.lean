import YM.Tawny.Table
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
open Rays Zinc Carnal Perla Perla.Fore
local notation "V"=>RawVec 10
abbrev Values (n:ℕ):= Flavor 6 →Fin n→ℂ
noncomputable def vectorZ (b:Flavor 6)(K:Fin 7 →ℂ): V:= K 0 • bee b + K 1 • beeA b + K 2 • lup b + K 3 • lapL b + K 4 • slashS b+ K 5 • slashT b+ K 6 • starV b
noncomputable def vectorY (K:Values 7):V:= ∑ b: Flavor 6,vectorZ b (K b)
local notation "K"=>Values
variable (v:K 7)(c:Fin 3→ℂ)(i:Axis)(p q:Multi 10)(J:Labels.Jet su)
noncomputable def ocean (c:Fin 3→ℂ): V:= c 0 • leapV+c 1 • lunar+c 2 • eulerV
noncomputable def plaza : K 7 ×(Fin 3→ℂ) →ₗ[ℂ] V where
 toFun x:= vectorY x.1+ ocean x.2
 map_add' x y:=by
    dsimp only [Prod.fst_add,Prod.snd_add]; have he(i:Flavor 6): vectorZ i ((x.1+y.1) i)=vectorZ i (x.1 i)+vectorZ i (y.1 i):=by unfold vectorZ; simp only [Pi.add_apply,add_smul]; abel
    simp_rw [vectorY,ocean,he,Finset.sum_add_distrib]; simp only [Pi.add_apply,add_smul]; abel
 map_smul' z x:=by unfold vectorY ocean vectorZ; simp only [Pi.smul_apply,smul_add,Prod.smul_fst,Prod.smul_snd,RingHom.id_apply, Finset.smul_sum,smul_smul,smul_eq_mul];
lemma fork(i j:Axis)(b:Flavor 6)(B:Spike):prism0 b p q (youthL a i j B)=0:=by unfold prism0; rw [LinearMap.comp_apply,LinearMap.comp_apply,skinP0,map_zero,map_zero]
local notation "A"=> vectorY v
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
local notation "T"=> (plaza (v,c)).val
lemma reflectY (x:Fin 7 →ℂ)(p q:Multi 10) (h:a ≠ b): prism0 a p q ((vectorZ b x).val i).val=0:=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [Submodule.coe_add,Submodule.coe_smul,AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_add,map_sub,bareB,h,false_and,if_false,sub_zero,add_zero,smul_zero,sum_const_zero,show ∀ i j, (med b i j (gamma j)).val= youthL b i j (gamma j) from fun _ _=>rfl,fork] -- instances
lemma reflectK (x:Fin 7 →ℂ)(p q:Axis)(hl:p≠q): prism1 a (0:Multi 10) 0 p q ((vectorZ b x).val p).val= if a=b then x 6 • gamma q else 0:=by
    simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val]; simp only [Submodule.coe_add,Submodule.coe_smul,AddSubmonoidClass.coe_finsetSum,map_add,map_sum,map_smul,beta_up,sea_up,shell0,shell1,shell2,basil_pond]; simp only [map_add,map_sub,bareC,sub_zero,add_zero,smul_zero,sum_const_zero,zero_add,show ∀ i j,(med b i j (gamma j)).val=youthL b i j (gamma j) from fun _ _=>rfl,measure_Y]; split; · simp [hl,Ne.symm hl,Complex.ofReal_mul,basis_eq,ite_smul,apply_ite]
    simp [*]
lemma oleap(i:Axis): (leapV).val i=∑ j:Axis,GE i j i i j:=rfl
lemma olun(i:Axis): lunar.val i=∑ j:Axis,∑ k:Axis, GE j k i j k:=rfl
lemma oeul(i:Axis): eulerV.val i=∑ j:Axis,∑ k:Axis,GE i j k k j:=rfl
lemma clr0(i j k l m:Axis):prism0 a p q (GE i j k l m).val=0:=clear_P a p q _
lemma clr1(i j k l m u v:Axis):prism1 a p q u v (GE i j k l m).val=0:= clear_K a u v p q _ -- order
lemma ve_m(p q:Multi 10): prism0 a p q ((ocean c).val i).val=0:=by
    simp only [ocean, Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul, oleap,olun,oeul,AddSubmonoidClass.coe_finsetSum,map_sum,clr0,Finset.sum_const_zero,smul_zero,add_zero]
lemma ve_X(p q:Multi 10)(m n:Axis):prism1 a p q m n ((ocean c).val i).val=0:=by
    simp only [ocean, Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul, oleap,olun,oeul,AddSubmonoidClass.coe_finsetSum,map_sum,clr1,Finset.sum_const_zero,smul_zero,add_zero]
lemma coast : prism0 a p q (T i).val=prism0 a p q ((vectorZ a (v a)).val i).val:=by
     change prism0 _ _ _ ((A+ocean c).val i).val=_; simp only [Submodule.coe_add,Pi.add_apply,map_add,ve_m,add_zero]; unfold vectorY; simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum]; rw [sum_eq_single a]; intro b _ h; exact reflectY a b i _ p q (Ne.symm h); simp
lemma coastX (j:Axis)(h:i≠j): prism1 a 0 0 i j (T i).val = v a 6 • gamma j:=by
     change prism1 _ _ _ _ _ ((A+ocean c).val i).val=_; simp only [Submodule.coe_add,Pi.add_apply,map_add,ve_X,add_zero]; unfold vectorY; simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum]; simp_rw [fun b=>reflectK a b _ i j h]; simp
end TableT
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.TableT.coast
#print axioms YM.Massive.Tawny.Cast.TableT.coastX
