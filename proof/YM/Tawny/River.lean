import YM.Tawny.Merry
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
local notation "Φ"=> vitality a v b' b' f g h X
local notation "R"=> rowC g f
private lemma seatT (k:Pinor): rowC (Pi.single k 1) f M= (M *ᵥ f) k:=by unfold rowC Matrix.mulVec dotProduct; rw [sum_eq_single k]; simp; intro t _ h; simp [Pi.single_apply,h,h.symm]; simp
lemma findT (hp:f≠0):∃ g:Pinor→ℂ,rowC g f 1≠0:=by
     by_contra! ht; apply hp; funext i; have h:=ht (Pi.single i 1); rw[seatT,Matrix.one_mulVec] at h; exact h
lemma findR (hp:f≠0) :∃ g:Pinor→ℂ,rowC g f (gamma i)≠0:=by
    by_contra! hz; have he: gamma i *ᵥ f=0:=by funext p; exact (seatT ..).symm.trans (hz (Pi.single p 1))
    apply hp; calc f= gamma i *ᵥ gamma i *ᵥ f := by rw [Matrix.mulVec_mulVec,Lat.gamma_sq,Matrix.one_mulVec]
                   _=_:=by rw[he,Matrix.mulVec_zero]
local notation "U"=> (0:Axis)
local notation "B"=> (1:Axis)
include h
lemma windC : Φ 8 (((windS a).val (i,j)).val)=v j*R (gamma i)-v i*R (gamma j):=by
    rw[W_wind]; change Φ _ (_- _)=_; rw[map_sub,phaseσ,phaseσ]; rw[if_pos,if_pos] <;> simp
lemma sunC : Φ 8 (((sunS a).val (i,j)).val)=v j * R (gamma i) + v i *R (gamma j):=by rw[W_sun]; change Φ _ (_+_)=_; rw [map_add,phaseσ,phaseσ]; rw [if_pos,if_pos] <;> simp
variable (x: Values 4)(p:Fin 4→ℂ)(u:Values 2)(r:Fin 3→ℂ)(y:Values 7)
set_option quotPrecheck false
local notation "w"=> vitality a v (0:Hue) 0 f g h 0
lemma lightW : w 8 ((arcS a).val (i,j)).val= - (w 8 ((windS a).val (i,j)).val):=by have he: projection ((windS a).val (i,j)+(arcS a).val (i,j))=0:=oppA ..; have hz:= (auditor a v (0:Hue) 0 f g h (0:Maxwell.TaylorTower su) (((windS a).val (i,j)+(arcS a).val (i,j)).val) ((Qeq _).mp he)).1; simp only [Submodule.coe_add,map_add] at hz; rw [add_comm] at hz; exact eq_neg_of_add_eq_zero_left hz -- states
omit h
lemma funds(hp:quoS (x,p)=0): p=0:=by
    apply axis_plot; intro X i j; have he: projection ((poseσ (x,p)).val (i,j))=0:= congr_fun hp (i,j); rw [← moneyσ (0: Flavor 6) (0:Axis→ℂ) (0:Hue) (0:Hue) i j (fun _=>0) (fun _=> 0) (vacancy _) X x p]; exact (auditor _ _ _ _ _ _ _ _ _ ((Qeq _).mp he)).2
lemma capT (hp:quoS (x,p)=0) : x a 0=0∧x a 1=0∧x a 2=0:=by
    obtain ⟨f,hF,hx⟩:= freedom; obtain ⟨g0,hg0⟩:=findT f hx; obtain ⟨g1,hg⟩:= findR U f hx; obtain ⟨g2,hg'⟩:= findR B f hx
    let W(v':Axis→ℂ)(g:Pinor→ℂ)(h:SlashV v' f):= vitality a v' (0:Hue) 0 f g h 0 8
    have ht(i j:Axis)(v)(g)(h:SlashV v f):W v g h ((axisσ a (x a)).val (i,j)).val=0:=by
          have he:projection ((poseσ (x,p)).val (i,j))=0:=congr_fun hp (i,j); unfold W; rw [← pricedσ a v (0:Hue) 0 i j f g h 0 x p]; exact (auditor _ _ _ _ _ _ _ _ _ ((Qeq _).mp he)).1
    have h0: x a 0=0:=by
         have hp:=ht U U (0:Axis→ℂ) g0 (vacancy f); unfold W at hp; simp only[axisσ, Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul] at hp; rw [W_wing,if_pos rfl,dimT,sunC,scalarR] at hp; change _=0 at hp; simp only[Pi.zero_apply,smul_zero,zero_mul,add_zero, ↓reduceIte,and_true] at hp; exact (mul_eq_zero.mp hp).resolve_right hg0
    have h1:x a 1=0:=by
         have he:=ht U B axis g2 hF; unfold W at he; simp only [axisσ, Submodule.coe_smul,Submodule.coe_add,Pi.add_apply,Pi.smul_apply,map_add,map_smul] at he; rw [h0,zero_smul,dimT,W_wing,if_neg (by decide),sunC] at he; change _=0 at he; simp only [axis,Matrix.cons_val_zero,Matrix.cons_val_one,Submodule.coe_zero, map_zero,zero_mul,one_mul,add_zero,zero_add,smul_zero] at he; exact (mul_eq_zero.mp he).resolve_right hg'
    have he:=ht U U axis g1 hF; unfold W at he; simp only [axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul] at he; rw [dimT,h0,h1,zero_smul,zero_smul,W_wing,if_pos rfl,sunC] at he; have hu:x a 2*(2* rowC g1 f (gamma U))=0:=by simp only [axis,Matrix.cons_val_zero,one_mul,smul_zero,zero_add,add_zero,← two_mul,mul_zero] at he; exact he
    exact ⟨h0,h1,(mul_eq_zero.mp hu).resolve_right (mul_ne_zero (by norm_num) hg)⟩
lemma debtT(hp:quoA u=0):u a 0=u a 1:=by
    obtain ⟨f,h,hf⟩:= freedom; obtain ⟨g,hg⟩:=findR B f hf; have he:projection ((poseα u).val (U,B))=0:= congr_fun hp (U,B); have ht:= (auditor a axis 0 0 f g h 0 _ ((Qeq _).mp he)).1; rw[pricedα a axis 0 0 U B f g h 0 u] at ht; simp only [axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul] at ht; rw [lightW,windC] at ht; have hz : u a 0* rowC g f (gamma B)=u a 1*rowC g f (gamma B):=by
          rw [show axis U=1 from rfl, show axis B=0 from rfl,zero_mul,one_mul,zero_sub,neg_neg] at ht; change u a 0 * - _ + u a 1 * _=0 at ht; linear_combination -ht -- sign?
    exact mul_right_cancel₀ hg hz
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.capT
#print axioms YM.Massive.Tawny.Cast.Drill.debtT
