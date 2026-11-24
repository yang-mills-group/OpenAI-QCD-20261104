import YM.Tawny.Scope
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
variable (v:Axis→ℂ)(b' c:Hue)(i j k:Axis)(M:Spike)(f g:Pinor→ℂ)(h:SlashV v f)(X:Maxwell.TaylorTower su)
local notation "Φ"=> vitality a v b' c f g h X
local notation "Ω"=>goldF a v b' c f g h X
local notation "R"=> rowC g f
local notation "L"=> leadR
local notation "Y"=> ηR
local notation "Z"=> (0:Multi 10)
local notation "YX"=>Values 7
include h
variable (x:Fin 7→ℂ)
private lemma epF (y:Multi 10)(S:Spike)(hy:y≠0): Φ 10 (bilinear b b S y Z)=0:=by simp only[epig _ _ _ _ _ _ _ _ _ _ _,hy,and_false,if_false]
lemma twoL: Φ 10 ((bee b).val i).val= if b=a∧b'=c then v i* R 1 else 0:=by
    rw [bee_val,beta_up,map_add, epF a b v b' c f g h X (L i) _ (hic i), add_zero,epig]; simp only [unit10,and_true]
lemma twistS: Φ 10 ((lup b).val i).val=if b=a∧b'=c then (v i*v i)* R (gamma i) else 0:=by rw[lup_val,shell0,basil_pond,map_sub,epF a b v b' c f g h X (Y i i) _ (hit i i), sub_zero,epig]; simp only[square10,and_true]
set_option quotPrecheck false
local notation "S"=> Φ 10 ((starV b).val i).val
lemma twistR : S= if b=a then ∑ j:Axis, ((BendR.ore (StressFlux.curl0 i j (lexY X 0))) c b') * R (gamma j) else 0:=by
    rw[star_val,AddSubmonoidClass.coe_finsetSum,map_sum]; simp_rw[show ∀ i j,(med b i j (gamma j)).val=youthL b i j (gamma j) from fun _ _=>rfl,mixedY]; split <;> simp[*]
local notation "W"=>RawVec 10
lemma zeroK(p:W)(hz:symbV p=0): Φ 10 (p.val i).val=0∧ Ω 10 (p.val i).val=0:= auditor a v b' c f g h X _ ((Qeq _).1 (congr_fun hz i))
lemma costV : Φ 10 ((vectorZ b x).val i).val= x 0* Φ 10 ((bee b).val i).val + x 2 *Φ 10 ((lup b).val i).val+ x 6 * S:=by
   obtain ⟨ht,hb,hZs,hZt,hf⟩:= tax_and b; simp only[vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,(zeroK a v b' c i f g h X _ ht).1,(zeroK a v b' c i f g h X _ hb).1,(zeroK a v b' c i f g h X _ hZs).1,(zeroK a v b' c i f g h X _ hZt).1, mul_zero,add_zero,smul_eq_mul]
lemma budgetV : Ω 10 ((vectorZ b x).val i).val=0:=by
    obtain ⟨ht,hb,hZs,hZt,hf⟩:=tax_and b; simp only [vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,(zeroK a v b' c i f g h X _ ht).2,(zeroK a v b' c i f g h X _ hb).2,(zeroK a v b' c i f g h X _ hZs).2,(zeroK a v b' c i f g h X _ hZt).2, smul_zero,add_zero]; rw [bee_val,lup_val,star_val, AddSubmonoidClass.coe_finsetSum]; simp only[beta_up,shell0,basil_pond,map_add,map_sub, p_hue, add_zero,map_sum,sub_zero, show ∀ j,(med b i j (gamma j)).val=youthL b i j (gamma j) from fun _=>rfl,fog_star,sum_const_zero,smul_zero]
variable (u:Values 7)(r:Fin 3→ℂ)
set_option quotPrecheck false
local notation "T"=>(plaza (u,r)).val
lemma tagsP : Φ 10 (T i).val= Φ 10 ((vectorZ a (u a)).val i).val:=by
     change Φ 10 ((vectorY u+ocean r).val i).val=_; have hz:=meter_v a v b' c i f g h X; simp only [Submodule.coe_add, Pi.add_apply,map_add,ocean,Submodule.coe_smul, Pi.smul_apply,map_smul,hz.1,hz.2.1,hz.2.2,smul_zero,add_zero,vectorY,AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,map_sum]; rw[sum_eq_single a]; intro b _ ht; rw [costV,twoL,twistS,twistR]; simp [ht]; simp
lemma monetary : Ω 10 (T i).val= r 0 *pages (lexY X) (leapV.val i) + r 1 *pages (lexY X) (lunar.val i):=by
     change Ω 10 ((vectorY u+ocean r).val i).val=_; have hz:=shine_e a v b' c i f g h X; simp only [Submodule.coe_add,Pi.add_apply,map_add,ocean,Submodule.coe_smul,Pi.smul_apply,map_smul,(zeroK a v b' c i f g h X _ (tax_and a).2.2.2.2).2, vectorY, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, map_sum,budgetV,hz.1,hz.2,sum_const_zero,smul_zero,zero_add,add_zero]; rfl
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.tagsP
#print axioms YM.Massive.Tawny.Cast.Drill.monetary
