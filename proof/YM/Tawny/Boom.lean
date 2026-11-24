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
namespace Dream.Clove
open TableT Carnal Rays Perla Zinc Quot
local notation "P"=> RawTensor 1 8
local notation "V"=> RawVec 10
local notation "H"=> (0: Multi 10)
local notation "L"=> leadR
local notation "A"=> ηR
local notation "D"=> projection
variable (i j k:Axis)
lemma Qeq (x:Label d): UV.Free.projection x=0 ↔ UV.Free.reduceEq x.val=0:= ⟨fun h=> congr_arg Subtype.val h,fun h=>Subtype.ext h⟩
private lemma hourS (i:Axis): AtNext i (0:Multi 8) (UV.first i):=by
     funext j; by_cases h:i=j; subst j; rw [update_self,nectar,if_pos rfl]; rfl
     rw [update_of_ne (Ne.symm h),nectar,if_neg h]; rfl
lemma oppH : D ((traceT a).val (i,j))=0:=by
    rw [W_trace]; split; · apply (Qeq _).2; rw [AddSubmonoidClass.coe_finsetSum]; simp only[amt,spinStressUnsymm, Finset.sum_sub_distrib,map_sub]; have h:= c_loss a a (0:Multi 8) 0 UV.first hourS (1:Spike); have hp:= b_loss a a (0:Multi 8) 0 UV.first hourS (1:Spike); simp only [one_mul,mul_one] at h hp; rw[h,hp,sub_zero]
    exact map_zero _
set_option maxHeartbeats 850000 in
private lemma addK {Z:Type*}[AddCommGroup Z](A₁ B D' F G K: Z): A₁-B - (D'-F) + (G+K) = F + -B + G+ (-D'+ A₁+K):=by abel
private abbrev e1 (a:Flavor 6)(M:Spike)(p q:Multi 8):=bilinear a a M p q
private lemma parts(K M:Axis→ Pol 8) (hk:i≠j)(hp:M i=(0:Pol 8))(ht:M j=0)(he:∀ l:Axis,l≠i→l≠j→K l=M l):∑ l:Axis,K l = K i+K j+ ∑ l:Axis,M l:=by
        rw [← add_sum_erase _ K (mem_univ i), ← add_sum_erase _ K (mem_erase.mpr ⟨(Ne.symm hk),mem_univ j⟩),← add_sum_erase _ M (mem_univ i),← add_sum_erase _ M (mem_erase.mpr ⟨(Ne.symm hk),mem_univ j⟩)]; rw [hp,ht, zero_add,zero_add,← add_assoc]; refine congr_arg _ (sum_congr rfl fun k hk=> he k (mem_erase.mp (mem_erase.mp hk).2).1 (mem_erase.mp hk).1)
local notation "t1"=>e1 a
local notation "s"=>gamma i*gamma j
local notation "r"=>UV.first i
local notation "q"=>UV.first j
local notation "F" l:arg=> t1 (trio l i j)
private lemma hB1(he:i≠j):
     (∑ k:Axis,t1 (gamma k *s) (UV.first k) 0)= t1 (gamma j) r 0+ -t1 (gamma i) q 0+∑ k:Axis,t1 (trio k i j) (UV.first k) 0 :=by
    let M(k:Axis):= gamma k *gamma i*gamma j
    have hu(k:Axis)(hk:k≠i)(hj:k≠j) : gamma k*(gamma i*gamma j)=trio k i j∧ (gamma i*gamma j)*gamma k=trio k i j:=by
        have hz:trio k i j=M k:=if_neg (by tauto)
        rw [hz]; unfold M; rw[← mul_assoc (gamma k)]; refine ⟨rfl,?_⟩; rw [Matrix.mul_assoc,clifford hj.symm,mul_neg,← Matrix.mul_assoc,clifford hk.symm,neg_mul,neg_neg]
    have h1 : gamma i*(gamma i*gamma j)=gamma j ∧ gamma j* (gamma i*gamma j)= -gamma i:=by
       constructor; · rw [← mul_assoc,Lat.gamma_sq,one_mul]
       rw [← mul_assoc, clifford (Ne.symm he),neg_mul,mul_assoc, Lat.gamma_sq,mul_one]
    let Z(k:Axis):= t1 (gamma k*s) (UV.first k) 0; let Q(k:Axis):= t1 (trio k i j) (UV.first k) 0; change (∑ k:Axis,Z k)=_; have hm :Z j= -t1 (gamma i) q 0:=by unfold Z e1; rw [h1.2,← neg_one_smul ℂ (gamma i),nourish]; exact neg_one_smul ℂ (bilinear a a (gamma i) q (0:Multi 8))
    rw [parts i j Z Q he (by simp[Q,e1,trio,bilinear]) (by simp[Q,e1,trio,bilinear]) (fun k hk hj=>by unfold Z; rw [(hu k hk hj).1]),hm]; unfold Z; rw [h1.1]
private lemma hB2(he:i≠j): (∑ k:Axis,t1 (s*gamma k) 0 (UV.first k)) = -t1 (gamma j) 0 r+t1 (gamma i) 0 q+∑ k:Axis,t1 (trio k i j) 0 (UV.first k):=by
     let M(k:Axis):=gamma k*gamma i*gamma j
     have hu(k:Axis)(hk:k≠i)(hj:k≠j) : gamma k*(gamma i*gamma j)=trio k i j∧ (gamma i*gamma j)*gamma k=trio k i j:=by
         have hz:trio k i j=M k:=if_neg (by tauto)
         rw [hz]; unfold M; rw[← mul_assoc (gamma k)]; refine ⟨rfl,?_⟩; rw [Matrix.mul_assoc,clifford hj.symm,mul_neg,← Matrix.mul_assoc,clifford hk.symm,neg_mul,neg_neg]
     have h1 : gamma i*(gamma i*gamma j)=gamma j ∧ gamma j* (gamma i*gamma j)= -gamma i:=by
        constructor; · rw [← mul_assoc,Lat.gamma_sq,one_mul]
        rw [← mul_assoc, clifford (Ne.symm he),neg_mul,mul_assoc, Lat.gamma_sq,mul_one]
     have h2 : (gamma i*gamma j)*gamma i= -gamma j ∧ gamma i*gamma j *gamma j=gamma i:=by
        constructor; rw[mul_assoc,clifford (Ne.symm he),mul_neg, h1.1]; rw[mul_assoc,Lat.gamma_sq,mul_one]
     let Z(k:Axis):=t1 (s*gamma k) 0 (UV.first k); let Q(k:Axis):= t1 (trio k i j) 0 (UV.first k); change (∑ k:Axis,Z k)=_; have hm: Z i= -t1 (gamma j) 0 r:=by unfold Z e1; rw [h2.1,← neg_one_smul ℂ (gamma j), nourish]; exact neg_one_smul ℂ (bilinear a a (gamma j) 0 r)
     rw [parts i j Z Q he (by simp[e1,Q,bilinear,trio]) (by simp[e1,Q,bilinear,trio]) (fun k hi hj=>by unfold Z; rw[(hu k hi hj).2]), hm]; unfold Z; rw [h2.2]
lemma oppA : D ((windS a).val (i,j)+(arcS a).val (i,j))=0:=by
    let M(k:Axis):= gamma k *gamma i *gamma j; let Z:Multi 8:=0
    rw [W_wind,W_arc, Qeq, Submodule.coe_add,Submodule.coe_sub,amt,amt,AddSubmonoidClass.coe_finsetSum]; unfold spinStressUnsymm
    simp only [trout,Finset.sum_add_distrib]; by_cases he:i=j
    · subst j; simp_rw [trio]; simp [bilinear]
    have hL:= b_loss a a (0:Multi 8) 0 UV.first hourS (gamma i*gamma j); have hR:=c_loss a a (0:Multi 8) 0 UV.first hourS (gamma i*gamma j)
    let R0(k:Axis):=t1 (trio k i j) 0 (UV.first k); let L0(k:Axis):=t1 (trio k i j) (UV.first k) 0
    have hP: reduceEq (t1 (gamma j) r 0 + -t1 (gamma i) q 0+(∑ k:Axis,L0 k))=0:= Eq.trans (congr_arg reduceEq (hB1 a i j he).symm) hL
    have hQ: reduceEq (-t1 (gamma j) 0 r+t1 (gamma i) 0 q+ (∑ k:Axis,R0 k))=0:=Eq.trans (congr_arg reduceEq (hB2 a i j he).symm) hR
    rw [add_comm (∑ k: Axis,R0 k) (∑ k:Axis,L0 k)]; refine Eq.trans (congr_arg reduceEq (show (t1 (gamma i) 0 q -t1 (gamma i) q 0 - (t1 (gamma j) 0 r-t1 (gamma j) r 0) + ((∑ k: Axis,L0 k)+(∑ k:Axis,R0 k)))= _ from addK _ _ _ _ _ _)) ?_
    rw [map_add,hP,hQ,add_zero]
-- V free zeros
lemma boo : D ((beeA a).val i)=0:=by
    rw [Qeq,sea_val,AddSubmonoidClass.coe_finsetSum]; simp_rw [sea_up,Finset.sum_add_distrib,map_add, show reduceEq (∑ j:Axis,bilinear a a (gamma i*gamma j) H (L j))=0 from c_loss a a H H L add_zeroL _, show reduceEq (∑ j:Axis,bilinear a a (gamma j*gamma i) (L j) H)=0 from b_loss a a H H L add_zeroL _,add_zero]
lemma gust : D ((slashS a).val i)=0:=by
    have h(j:Axis): AtNext j (L i) (A i j):=add_next ..
    rw [Qeq,s_val,AddSubmonoidClass.coe_finsetSum]; simp_rw[shell1,basil_pond, Finset.sum_sub_distrib,map_sub]; have hz:= c_loss a a _ H _ h (1:Spike); have he:= b_loss a a _ H _ h (1:Spike); simp only[mul_one,one_mul] at hz he; rw [hz,he,sub_zero]
lemma gradeR : D ((slashT a).val i)=0:=by
    have h:= c_loss a a H (L i) L add_zeroL (1:Spike); have hp:= b_loss a a H (L i) L add_zeroL (1:Spike); simp only [mul_one,one_mul] at h hp; rw[Qeq,t_val,AddSubmonoidClass.coe_finsetSum]; simp_rw [shell2,basil_pond,Finset.sum_sub_distrib,map_sub]; rw[h,hp,sub_zero]
end Dream.Clove
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Dream.Clove.oppA
#print axioms YM.Massive.Tawny.Cast.Dream.Clove.gust
