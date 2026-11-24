import YM.Avian.Icarus
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Seals
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open StressFlux (pairDeriv curl0 curl1 leg0 leg1)
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
local notation "Q★"=> (0:Multi 8)
local notation "Y"=>UV.first
local notation "Z"=>(0:Multi 10)
local notation "B"=> leadR
local notation "X"=> ηR
local notation "I₁"=> (0:Axis)
local notation "J₁"=> (1:Axis)
variable (a b:Flavor 6) (x y:ℂ)(u:Values 4)(z:Fin 4→ℂ)(v:Values 2)(i j:Axis)
local notation "T" p:arg q:arg i:arg j:arg => prism0 a p q ((poseσ (u,z)).val (i,j)).val
local notation "Φ" p:arg q:arg i:arg j:arg=>prism0 a p q ((poseα v).val (i,j)).val
lemma sLead0 : T Q★ Q★ I₁ I₁ = u a 0 • (1:Spike):=by
     rw [recognize,railσ0]
lemma aLead0 : Φ Q★ Q★ I₁ I₁ = 0:=by
     rw[recognizeA]
     simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_arc,W_wind,trout,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals first|norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] | module
lemma sLead1 : T Q★ Q★ J₁ I₁ = 0:=by
     rw[recognize]
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
lemma aLead1 : Φ Q★ Q★ J₁ I₁ = 0:=by
     rw[recognizeA]
     simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_arc,W_wind,trout,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals first|norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] | module
lemma sLead2 : T Q★ (Y I₁) I₁ I₁ = ((u a 1*2+u a 2*2+u a 3):ℂ) • gamma I₁:=by
     rw [recognize,railσ3]; module
lemma aLead2 : Φ Q★ (Y I₁) I₁ I₁ = 0:=by
     let X':= poseα v; let V:= (I₁,I₁); have he:X'.val V=0:=by
           have hp:X'.val V=(-1:ℂ) • X'.val V:=(show Meaning _ _ _ _ _ _ from X'.property).sym V
           let N:= (X'.val V).val; have hh:N= -N:=by have he:=congr_arg Subtype.val hp; change N=(-1:ℂ) • N at he; exact he.trans (neg_one_smul ℂ N) -- rewrite both risky
           have hf : (2:ℂ) • N=0:=by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hh
           exact Subtype.ext ((smul_eq_zero.mp hf).resolve_left (by norm_num))
     rw [show (poseα v).val (0,0)=0 from he,Submodule.coe_zero,map_zero]
lemma sLead3 : T Q★ (Y J₁) J₁ I₁ = u a 1 • gamma I₁:=by
     rw[recognize]
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
lemma aLead3 : Φ Q★ (Y J₁) J₁ I₁ =  -(v a 0 • gamma I₁):=by
     rw[recognizeA]
     simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_arc,W_wind,trout,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals first|norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] | module
lemma sLead4 : T Q★ (Y J₁) I₁ I₁ = u a 3 • gamma J₁:=by
     rw [recognize,railσ2]
lemma aLead4 : Φ Q★ (Y J₁) I₁ I₁ = 0:=by
     let X':= poseα v; let V:= (I₁,I₁); have he:X'.val V=0:=by
           have hp:X'.val V=(-1:ℂ) • X'.val V:=(show Meaning _ _ _ _ _ _ from X'.property).sym V
           let N:= (X'.val V).val; have hh:N= -N:=by have he:=congr_arg Subtype.val hp; change N=(-1:ℂ) • N at he; exact he.trans (neg_one_smul ℂ N) -- rewrite both risky
           have hf : (2:ℂ) • N=0:=by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hh
           exact Subtype.ext ((smul_eq_zero.mp hf).resolve_left (by norm_num))
     rw [show (poseα v).val (0,0)=0 from he,Submodule.coe_zero,map_zero]
lemma sLead5 : T Q★ (Y I₁) J₁ I₁ = u a 1 • gamma J₁:=by
     rw[recognize]
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
lemma aLead5 : Φ Q★ (Y I₁) J₁ I₁ = v a 0 • gamma J₁:=by
     rw[recognizeA]
     simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_arc,W_wind,trout,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals first|norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] | module
lemma sLead6 : T (Y J₁) Q★ I₁ I₁ = -(u a 3 • gamma J₁):=by
     rw[recognize]
     simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,W_mass,W_trace,W_wing,W_sun,amt,spinStressUnsymm,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,map_add,map_sub,map_sum,bareB]
     simp +decide only[Submodule.coe_add,map_add,reduceIte, AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_sum,map_zero,amt, spinStressUnsymm,show ∀ h,(solstice a 1 Q★ Q★ h).val= bilinear a a 1 Q★ Q★ from fun _=>rfl,bareB,map_sub,add_zero,zero_add,sub_zero,smul_zero, first_eq,highV,fun i=>Ne.symm (highV i)]
     all_goals norm_num [Fin.sum_univ_four,Fin.ext_iff,trio] -- edit
lemma aLead6 : Φ (Y J₁) Q★ I₁ I₁ = 0:=by
     let X':= poseα v; let V:= (I₁,I₁); have he:X'.val V=0:=by
           have hp:X'.val V=(-1:ℂ) • X'.val V:=(show Meaning _ _ _ _ _ _ from X'.property).sym V
           let N:= (X'.val V).val; have hh:N= -N:=by have he:=congr_arg Subtype.val hp; change N=(-1:ℂ) • N at he; exact he.trans (neg_one_smul ℂ N) -- rewrite both risky
           have hf : (2:ℂ) • N=0:=by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hh
           exact Subtype.ext ((smul_eq_zero.mp hf).resolve_left (by norm_num))
     rw [show (poseα v).val (0,0)=0 from he,Submodule.coe_zero,map_zero]
end YM.Massive.Patria.Gall.Seals
#print axioms YM.Massive.Patria.Gall.Seals.aLead6
