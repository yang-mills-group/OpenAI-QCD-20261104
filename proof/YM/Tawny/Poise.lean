import YM.Tawny.Quash
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
noncomputable def axisσ (a:Flavor 6)(x:Fin 4→ℂ):RawTensor 1 8:= x 0 • scalarS a+x 1 • sunS a+x 2 • wingS a+x 3 • traceT a
noncomputable def axisα (a:Flavor 6)(x:Fin 2→ℂ):RawTensor (-1) 8:=x 0 • windS a+x 1 • arcS a
noncomputable def gaugeσ (z:Fin 4→ℂ): RawTensor 1 8:= z 0 • epi+z 1 • spire+z 2 • shadow+z 3 • eclipse -- corresponding to replacing spire with solid.Normalize.T.G later.
noncomputable def poseσT (u:Values 4): RawTensor 1 8:=∑ i: Flavor 6,axisσ i (u i)
noncomputable def poseσ : Values 4 ×(Fin 4→ℂ)→ₗ[ℂ] RawTensor 1 8 where
 toFun x:=poseσT x.1+gaugeσ x.2
 map_add' x y:=by dsimp only [Prod.fst_add,Prod.snd_add]; have he(i:Flavor 6):axisσ i ((x.1+y.1) i)=axisσ i (x.1 i)+axisσ i (y.1 i):=by simp only[axisσ,Pi.add_apply,add_smul]; abel
                  simp_rw [poseσT,he, Finset.sum_add_distrib]; unfold gaugeσ; simp only[Pi.add_apply,add_smul]; abel
 map_smul' z x:=by unfold poseσT axisσ gaugeσ; simp only [RingHom.id_apply,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_add,smul_sum,smul_smul,smul_eq_mul]
noncomputable def poseα : Values 2→ₗ[ℂ] RawTensor (-1) 8 where
 toFun x:= ∑ i:Flavor 6,axisα i (x i)
 map_add' x y:=by have he(i:Flavor 6):axisα i ((x+y) i)=axisα i (x i)+axisα i (y i):=by simp only[axisα,Pi.add_apply,add_smul]; abel
                  simp_rw[he,Finset.sum_add_distrib]
 map_smul' z x:=by unfold axisα; simp only [RingHom.id_apply,Pi.smul_apply,smul_add,smul_sum,smul_smul,smul_eq_mul]
local notation "SX"=>RawTensor 1 8
local notation "AX"=>RawTensor (-1) 8
variable (x:Fin 4→ℂ)(y:Fin 2→ℂ)(p q: Multi 8)(i j k:Axis)
local notation "Z"=> (0:Multi 8)
local notation "L"=> UV.first
-- make equations with projections on values rather than wrapped linear map
lemma W_sun:(sunS a).val (i,j)=alter a i j + alter a j i:=by change _+ (1:ℂ) • _= _; rw[one_smul]
lemma W_wind:(windS a).val (i,j)=alter a i j-alter a j i:=by change _+(-1:ℂ) • _=_; apply Eq.trans (b:=alter a i j + -(alter a j i)); exact congr_arg _ (neg_one_smul ℂ (alter a j i)); exact Eq.symm (sub_eq_add_neg (alter a i j) (alter a j i))
lemma W_wing :(wingS a).val (i,j)=if i=j then (sunS a).val (i,j) else 0:=rfl
lemma W_trace:(traceT a).val (i,j)=if i=j then ∑ k:Axis,alter a k k else 0:=rfl
lemma W_mass : (scalarS a).val (i,j)=if i=j then solstice a 1 Z Z (by rw [cost_root]; decide) else 0:=rfl
lemma W_arc:(arcS a).val (i,j)=∑ k:Axis,triple a k i j:=rfl
set_option quotPrecheck false
local notation "σ" i:arg j:arg=> ((axisσ b x).val (i,j)).val
set_option linter.unusedSimpArgs false
local notation "α" i:arg j:arg=> ((axisα b y).val (i,j)).val
lemma gauge_anc : prism0 a p q ((gaugeσ x).val (i,j)).val=0:=by
    simp only [gaugeσ, Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul]; rw [epi_at,spire_val,shadow_val,dark]; split <;> simp only [smul_zero,zero_smul, AddSubmonoidClass.coe_finsetSum,_root_.map_sum,show ∀i j a' b', prism0 a p q (GG i j a' b').val=0 from fun i j a' b'=>clear_P .., sum_const_zero, show prism0 a p q (UV.unit 8)=0 from clear_P .., Submodule.coe_zero, map_zero,add_zero]
lemma alloy (h:a≠b): prism0 a p q (σ i j)=0:=by
    simp only[axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply, Pi.smul_apply,map_add,map_smul]; rw[W_mass,W_trace,W_wing]; split_ifs <;> simp only [W_sun, AddSubmonoidClass.coe_finsetSum, Submodule.coe_add,Submodule.coe_sub,Submodule.coe_zero,map_zero,map_sum,map_add,map_sub,sum_add_distrib,sum_sub_distrib,amt,spinStressUnsymm,trout,show ∀(h:spinWeight Z+spinWeight Z ≤8),(solstice b 1 Z Z h).val=bilinear b b 1 Z Z from fun _=>rfl,bareB,h,false_and,if_false,add_zero,sub_zero,sum_const_zero,smul_zero]
lemma alloyα (h:a≠b): prism0 a p q (α i j)=0:=by
    simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul]; rw[W_wind,W_arc]; simp only[AddSubmonoidClass.coe_finsetSum,Submodule.coe_sub, map_sub,map_sum,amt,trout,map_add,spinStressUnsymm,bareB,h,false_and,if_false,sub_zero,add_zero,sum_const_zero,smul_zero]
variable (u:Values 4)(Yv:Values 2)(z:Fin 4→ℂ)
lemma recognize : prism0 a p q (((poseσ (u,z)).val (i,j)).val)= prism0 a p q (((axisσ a (u a)).val (i,j)).val):=by
     change prism0 _ _ _ ((poseσT u+gaugeσ z).val (i,j)).val=_; simp only [Submodule.coe_add, Pi.add_apply, map_add,gauge_anc,add_zero,poseσT,AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum]; rw[sum_eq_single a]; intro b _ h; exact alloy a b _ p q i j (Ne.symm h); simp
set_option maxRecDepth 4800 in
lemma recognizeA : prism0 a p q ((poseα Yv).val (i,j)).val=prism0 a p q (((axisα a (Yv a)).val (i,j)).val):=by
     rw [show poseα Yv = ∑ b:Flavor 6,axisα b (Yv b) from rfl]; simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum]; rw [sum_eq_single a]; intro b _ h; exact alloyα a b _ p q i j (Ne.symm h); simp
end TableT
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.TableT.recognize
