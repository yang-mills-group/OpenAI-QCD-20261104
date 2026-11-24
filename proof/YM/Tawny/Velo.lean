import YM.Tawny.Dirge
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
open TableT Carnal Rays Perla Zinc Perla.Fore Dream Dream.Clove LinearMap
open scoped Kronecker
variable (x:Values 4)(p:Fin 4→ℂ)(u:Values 2)(r:Fin 3→ℂ)(y:Values 7)
local notation "KQ"=> quoS.ker
local notation "E"=>quoA.ker
local notation "F"=> quoV.ker
lemma omegaS : quoS (x,p)=0 ↔ p=0∧∀ a, x a 0=0∧x a 1=0∧x a 2=0:= by
     constructor; exact fun h=> ⟨funds x p h,fun a=>capT a x p h⟩; rintro ⟨rfl,h⟩
     change symbS 1 (poseσT x+gaugeσ 0)=0; simp only [gaugeσ,poseσT,Pi.zero_apply, zero_smul,add_zero,map_zero,map_sum,axisσ,map_add,map_smul,fun a=>(h a).1, fun a=>(h a).2.1, fun a=>(h a).2.2, simplify_s,smul_zero,sum_const_zero]
lemma omegaA : quoA u=0 ↔ ∀ a,u a 0=u a 1:=by
     constructor; exact fun h a=> debtT a u h; intro h; change symbS (-1) (poseα u)=_; rw [show poseα u=∑ a:Flavor 6,axisα a (u a) from rfl]; rw [map_sum]; refine sum_eq_zero fun i _=>?_; unfold axisα; rw [map_add,map_smul,map_smul,simplify_a,h]; rw[show u i 1 • -symbS (-1) (windS i)= -(u i 1 • symbS (-1) (windS i)) from funext fun j=> smul_neg (u i 1) ((symbS (-1) (windS i)) j)]; exact funext fun a=> add_neg_cancel (u i 1 • (symbS (-1) (windS i)) a)
lemma omegaV : quoV (y,r)=0 ↔ r 0=0∧r 1=0∧∀ a,y a 0=0∧y a 2=0∧y a 6=0:=by
     constructor; intro h; exact ⟨(pricesV r y h).1,(pricesV r y h).2,fun a=>soundV a r y h⟩; rintro ⟨ht,h1,h2⟩
     change symbV (vectorY y+ ocean r)=_; unfold vectorY ocean; rw [_root_.map_add,map_sum]; simp only [_root_.map_add,map_smul,tax_and 0 |>.2.2.2.2, ht,h1,smul_zero,zero_smul,map_zero,add_zero]; apply sum_eq_zero; intro i _; obtain ⟨hA,hB,hC,hE,hQ⟩:=tax_and i; obtain ⟨h0,h2,h6⟩:=h2 i; simp only[vectorZ,map_add,map_smul,h0,h2,h6,hA,hB,hC,hE,hQ,zero_smul,smul_zero,map_zero,add_zero]
abbrev Ink:= Flavor 6 →ℂ
noncomputable def seatS : Ink→ₗ[ℂ] KQ where
  toFun x:= ⟨(fun i: Flavor 6=>![0,0,0,x i], 0), mem_ker.mpr ((omegaS ..).2 ⟨rfl,fun _=>⟨rfl,rfl,rfl⟩⟩)⟩
  map_add' x y:=by
     apply Subtype.ext; apply Prod.ext; funext i j; fin_cases j <;> first|exact (zero_add (0:ℂ)).symm|rfl
     change (0:Fin 4→ℂ)=0+0; rw [zero_add]
  map_smul' z x:=by
     apply Subtype.ext; apply Prod.ext; funext i j; fin_cases j <;> first|exact (mul_zero z).symm|rfl
     change (0:Fin 4→ℂ)= (z:ℂ) • 0; rw[smul_zero]
lemma onS : Bijective seatS:=by
     constructor
     · intro x y h; funext i; exact congr_fun (congr_fun (congr_arg Prod.fst (congr_arg Subtype.val h)) i) (3:Fin 4)
     rintro ⟨⟨p,q⟩,h⟩; obtain ⟨hq,hz⟩:= (omegaS p q).mp (mem_ker.1 h); subst q; refine ⟨fun i=>p i 3, Subtype.ext (Prod.ext ?_ rfl)⟩; funext i j; fin_cases j; exact (hz i).1.symm; exact (hz i).2.1.symm; exact (hz i).2.2.symm; rfl
noncomputable def seatA : Ink→ₗ[ℂ] E where
  toFun x:= ⟨fun i j=> x i,mem_ker.2 ((omegaA _).2 fun _=>rfl)⟩
  map_add' x y:=rfl
  map_smul' z x:=rfl
lemma onA : Bijective seatA:=by
    constructor
    · intro x y h; funext i; exact congr_fun (congr_fun (congr_arg Subtype.val h) i) (0:Fin 2)
    rintro ⟨x,h⟩; have hp:=(omegaA x).mp (mem_ker.1 h); refine ⟨fun i=> x i 0, Subtype.ext ?_⟩; funext i j; fin_cases j; rfl; exact hp i
noncomputable def seatV : Values 4 × ℂ →ₗ[ℂ] F where
  toFun x := ⟨(fun i=>![0,x.1 i 0,0,x.1 i 1,x.1 i 2,x.1 i 3,0],![0,0,x.2]),mem_ker.mpr ((omegaV ..).2 ⟨rfl,rfl,fun i=>⟨rfl,rfl,rfl⟩⟩)⟩ -- omega order r first? omegaV r y
  map_add' x y:=by
       apply Subtype.ext; apply Prod.ext; funext i j; fin_cases j <;> first|exact (zero_add (0:ℂ)).symm|rfl
       funext j; fin_cases j <;> first|exact (zero_add (0:ℂ)).symm|rfl
  map_smul' z x:=by
       apply Subtype.ext; apply Prod.ext; funext i j; fin_cases j <;> first|exact (mul_zero z).symm|rfl
       funext j; fin_cases j <;> first|exact (mul_zero z).symm|rfl
lemma onV : Bijective seatV:=by
    constructor
    · intro x y h; apply Prod.ext
      · funext i j; have he:= congr_fun (congr_arg Prod.fst (congr_arg Subtype.val h)) i; fin_cases j
        · exact congr_fun he (1:Fin 7)
        · exact congr_fun he (3:Fin 7)
        · exact congr_fun he (4:Fin 7)
        · exact congr_fun he (5:Fin 7)
      exact congr_fun (congr_arg Prod.snd (congr_arg Subtype.val h)) (2:Fin 3)
    rintro ⟨⟨v,r⟩,h⟩; obtain ⟨hr,h1,hV⟩:=(omegaV r v).1 (mem_ker.1 h); refine ⟨(fun a=>![v a 1,v a 3,v a 4,v a 5],r 2),Subtype.ext (Prod.ext ?_ ?_)⟩
    · funext i j; fin_cases j; exact (hV i).1.symm; rfl; exact (hV i).2.1.symm; rfl; rfl; rfl; exact (hV i).2.2.symm
    funext i; fin_cases i; exact hr.symm; exact h1.symm; rfl
lemma tall : Module.finrank ℂ (symbS 1).range=22 ∧ Module.finrank ℂ (symbS (-1)).range=6 ∧ Module.finrank ℂ symbV.range=20:=by
    haveI SI : Module.Finite ℂ (Values 4) := inferInstance; haveI FI: Module.Finite ℂ (Values 7):=inferInstance
    have hs: KQ = quoS.ker:=rfl
    have h1:=LinearMap.finrank_range_add_finrank_ker (K:=ℂ) (V:=Values 4×(Fin 4→ℂ)) (V₂:=Axis×Axis→ UV.Free.Symbol 8) quoS; have h2:= LinearMap.finrank_range_add_finrank_ker (K:=ℂ) (V:=Values 2) (V₂:=Axis×Axis→ UV.Free.Symbol 8) quoA; have h3:=LinearMap.finrank_range_add_finrank_ker (K:=ℂ) (V:=Values 7 × (Fin 3→ℂ)) (V₂:= Axis→UV.Free.Symbol 10) quoV; rw [←(LinearEquiv.ofBijective seatS onS).finrank_eq,Module.finrank_prod,tolls,Module.finrank_fin_fun] at h1; rw[←(LinearEquiv.ofBijective seatA onA).finrank_eq,tolls] at h2; rw [←(LinearEquiv.ofBijective seatV onV).finrank_eq,Module.finrank_prod,tolls,Module.finrank_self, Module.finrank_prod,tolls,Module.finrank_fin_fun] at h3;
    have he:Module.finrank ℂ Ink=6:=Module.finrank_fin_fun ℂ
    have hx:quoS.range=(symbS 1).range:=by unfold quoS; exact LinearMap.range_comp_of_range_eq_top _ ((LinearMap.range_eq_top (f:=poseσ)).mpr bona.1.2)
    have ht:quoA.range=(symbS (-1)).range:=by unfold quoA; exact LinearMap.range_comp_of_range_eq_top _ ((LinearMap.range_eq_top (f:=poseα)).mpr bona.2.2)
    have hp:quoV.range=symbV.range:=by unfold quoV; exact LinearMap.range_comp_of_range_eq_top _ ((LinearMap.range_eq_top (f:=plaza)).mpr certified.2)
    rw [←hx,←ht,←hp]; have hF:Module.finrank ℂ (Fin 4→ℂ)=4:=Module.finrank_fin_fun ℂ; have hG:Module.finrank ℂ (Fin 3→ℂ)=3:=Module.finrank_fin_fun ℂ; omega
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.tall
