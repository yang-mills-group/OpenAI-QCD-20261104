import YM.Tawny.Carnal
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Carnal
open Rays
variable (s:Signed)(w:EuPin)(h:w.Lifts s)(i j k l:Axis)
local notation "Z"=> RawVec 10
local notation "L" => leadR
local notation "R"=> ηR
local notation "U"=> (0:Multi 10)
noncomputable def beta (a:Flavor 6)(i:Axis):= mixed a 1 U (L i) (by rw[gradeL,gradeV]; decide)
noncomputable def sea (a:Flavor 6)(i j:Axis):= mixed a (gamma i*gamma j) U (L j) (by rw[gradeL,gradeV]; decide)
noncomputable def basil(a:Flavor 6)(i:Axis)(p q:Multi 10)(h:spinWeight p+spinWeight q≤10):=mixed a (gamma i) p q h
noncomputable def shell0(a:Flavor 6)(i j:Axis):= basil a i U (R j j) (by rw [gradeV,gradeH])
noncomputable def shell1(a:Flavor 6)(i j:Axis):= basil a j U (R i j) (by rw[gradeV,gradeH])
noncomputable def shell2(a:Flavor 6)(i j:Axis):= basil a j (L j) (L i) (by rw [gradeL,gradeL])
local notation "σ" i:arg=> (signT s i:ℂ)
local notation "K"=> s.perm
include h
private lemma chargeB : pinAct w ((beta a i).val)= σ i • (beta a (K i)).val:=by
    have he : conjug w (1:Spike)=(1:ℂ) • (1:Spike):=by rw [conjug,mul_one,inv1,one_smul] -- scalar annotation
    have ht:=paidM a (1:Spike) U (L i) (by rw[gradeL,gradeV]; decide) s w h (1:ℂ) _ he (by rw[truck_one]; exact he ); simp_rw[marked_root,markedL,hem_ground,hem_lead,one_mul,mul_one] at ht; exact ht
private lemma chargedB : pinAct w ((sea a i j).val)= σ i • (sea a (K i) (K j)).val:=by
    have he : conjug w (gamma i*gamma j)=(σ i *σ j) • (gamma (K i) *gamma (K j)):=by rw [L_up,E_sigma s w h,E_sigma s w h,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    have hx: conjug w (truck (gamma i*gamma j))= (σ i *σ j) • truck (gamma (K i)*gamma (K j)):=by rw [antiMul,antiT,antiT,antiMul,antiT,antiT,neg_mul_neg,neg_mul_neg,L_up,E_sigma s w h,E_sigma s w h,Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm (σ j)]
    have ht:=paidM a (gamma i*gamma j) U (L j) (by rw[gradeV,gradeL]; decide) s w h _ _ he hx; simp_rw[hem_ground,hem_lead] at ht; rw [marked_root,markedL,one_mul,mul_left_comm,← Complex.ofReal_mul (signT s j), UV.sign_sq,Complex.ofReal_one,mul_one] at ht; exact ht
private lemma raw_gear (p q:Multi 10)(hp:spinWeight p+spinWeight q ≤ 10): pinAct w ((basil a i p q hp).val)=(((marked s p*marked s q:ℝ):ℂ)*σ i) • (basil a (K i) (hem s p) (hem s q) (by rwa [borderBuck,borderBuck])).val:=paidM a _ _ _ _ s w h _ _ (E_sigma s w h i) (by rw[antiT,antiT,conjug,mul_neg,neg_mul]; change -(conjug w _) =_; rw [E_sigma s w h,smul_neg])
private lemma marked2 : marked s (R i i)=1:=by rw [markedH, UV.sign_sq]
private lemma gear0 : pinAct w ((shell0 a i j).val)=σ i • (shell0 a (K i) (K j)).val:=by unfold shell0; rw [raw_gear a s w h]; simp only[hem_ground,hem_η]; rw[marked_root,markedH, UV.sign_sq,one_mul,Complex.ofReal_one,one_mul]
private lemma gear1: pinAct w ((shell1 a i j).val)= σ i • (shell1 a (K i) (K j)).val:=by unfold shell1; rw [raw_gear a s w h]; simp only[hem_ground,hem_η]; rw[marked_root,markedH,one_mul,← Complex.ofReal_mul, mul_assoc,UV.sign_sq,mul_one]
private lemma gear2: pinAct w ((shell2 a i j).val)= σ i • (shell2 a (K i) (K j)).val:=by unfold shell2; rw [raw_gear a s w h]; simp only[hem_lead]; rw[markedL,markedL, mul_comm (signT s j) (signT s i),← Complex.ofReal_mul, mul_assoc,UV.sign_sq,mul_one]
omit h
noncomputable def meltV (v:Axis→Axis→Label 10)(h:∀ i j,v i j∈ Pe 10)(ht:∀ (s: Signed)(w:EuPin),w.Lifts s→∀ i j,pinAct w (v i j).val=(↑(signT s i):ℂ) • (v (s.perm i) (s.perm j)).val): Z:= stick (fun i=>∑ j:Axis,v i j) (fun i=> Submodule.sum_mem _ (fun j _=> h i j)) (by intro s w h i; simp_rw [AddSubmonoidClass.coe_finsetSum, map_sum,ht _ _ h,← smul_sum]; exact congr_arg (_ • ·) (Equiv.sum_comp s.perm (fun j=> (v (s.perm i) j).val)))
noncomputable def bee : Z:= stick (beta a) (fun _=> munity ..) (fun s w h i=> chargeB a s w h i)
noncomputable def beeA : Z:= meltV (sea a) (fun _ _=> munity ..) (fun s w h=> chargedB a s w h)
noncomputable def lup : Z:= stick (fun i=>shell0 a i i) (fun _=> munity ..) (fun s w h i=> gear0 a s w h i i)
noncomputable def lapL : Z:= meltV (shell0 a) (fun _ _=> munity ..) (fun s w h => gear0 a s w h)
noncomputable def slashS : Z:= meltV (shell1 a) (fun _ _=> munity ..) (fun s w h=> gear1 a s w h)
noncomputable def slashT : Z:= meltV (shell2 a) (fun _ _=> munity ..) (fun s w h=> gear2 a s w h)
variable (p q:Multi 10)(h:spinWeight p+spinWeight q≤10)
lemma basil_pond : (basil a i p q h).val=bilinear a a (gamma i) p q-bilinear a a (gamma i) q p:=by unfold basil mixed; rw[antiT,push_neg,sub_eq_add_neg]; rfl
lemma beta_up : (beta a i).val= bilinear a a 1 U (L i)+bilinear a a 1 (L i) U:=by unfold beta mixed; rw[truck_one]; rfl
lemma sea_up : (sea a i j).val=bilinear a a (gamma i*gamma j) U (L j)+ bilinear a a (gamma j*gamma i) (L j) U:=by unfold sea mixed; rw[antiMul,antiT,antiT,neg_mul_neg]; rfl
end Carnal
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Carnal.beeA
#print axioms YM.Massive.Tawny.Cast.Carnal.slashS
