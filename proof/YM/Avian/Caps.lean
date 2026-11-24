import YM.Avian.BloomD
/-! Symbol tensor estimates respect averaging. Grouped C rows declared *fixed*. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Jewels
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper Tawny Cast Patria.Rolls Patria.Rolls.Attain Seals
variable {S:Scheme}{R:Side}{i N:ℕ}(A:Run S N R 6)(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore 8)(hT:Rubric sym B)(F:PatchMix 8)(hf:OrderMix A T sym B (i:=0) F)
variable (x:ℂ)(Q:RawTensor x 8)
set_option quotPrecheck false
local notation "c"=> S.side R N
local notation "M★"=> S.side R 0
local notation "W'"=> A.density 0
local notation "Sχ"=> skyU A B F x Q
local notation "Yχ"=> vine A B F x Q
local notation "Vχ"=> divine A B F x Q
variable (hA:A.Actual)(hI:∀ t b i, Lat.Invariant (B t b i))(i j:Axis)(C:Axis→Axis→Label 10)(he:∀ i j, Tally T 0 (C i j) (A.density 0) (trolley A (vine A B F x Q i j) (shelV j) 0 0))
local notation "cR"=>path A B F x Q
local notation "Aχ"=>castG A B F x Q
variable (D:RawVec 10)(hD:∀ j: Axis,D.val j=∑ i:Axis,C i j)
variable (P:BudgetPoint)(n m:ℕ)(t a:ℝ)(hN:10 ≤ P.order)(hm:6 ≤ n)(hC:2 < m)(ht:0<t)(hQ:∀ i j:Axis, Tutor 0 P (Canvas.foil (A.density 0) ((path A B F x Q i j 0))) t n m a)
local notation "KT"=> port a (S.side R 0) t
lemma dueT(F G:Axis→ℂ)(A:ℝ)(h:∀ i,‖F i-G i‖ ≤ A) : ‖(∑ i,F i)-(∑ i,G i)‖ ≤ 4*A:=by rw[←Finset.sum_sub_distrib]; exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=> h i)).trans_eq (by rw[sum_const,nsmul_eq_mul,card_univ]; norm_num[Axis]))
include hD he hQ hA hT hf
variable (p:Flavor 6)(i1 i2:Pinor)
local notation "vr" p:arg q:arg=>loaf p q
local notation "Z1"=> (0:Multi 10)
local notation "V1"=> (0:Multi 8)
local notation "QX" x:arg=> Q.val (x,(0:Axis))
local notation "l" a:arg b:arg=> loaf a b p i1 i2
lemma force1 (X Y:Multi 10)(M:Axis→ℂ)(h:∀ i:Axis,‖(l X Y) (C i 0)-M i‖ ≤ KT) : ‖qv p X Y D i1 i2 - ∑ i:Axis,M i‖ ≤4*KT:=by
     change ‖(l X Y) (D.val _) - _‖ ≤ _; rw[hD,map_sum]; exact dueT _ _ _ h
variable (w u: Axis)
include ht hm hC
local notation "ℓ"=> UV.first
open Rays
local notation "Yp" a:arg=> leadR a
local notation "Zp" a:arg b:arg=>ηR a b
lemma facet_lead : ‖qv p Z1 (leadR w) D i1 i2-ts x p V1 V1 w Q i1 i2‖ ≤ 4*KT:=by
    let f(i:Axis):= piv w i * ((l V1 V1) (QX i)); have hp:(∑ i:Axis,f i)= ts x p V1 V1 w Q i1 i2:=by unfold f piv; simp[ite_mul]; rfl
    rw [←hp]; apply force1 A T sym B hT F hf x Q hA C he D hD P n m t a hQ p i1 i2; intro i; apply impetus w T i1 i2 i W' (cR i 0 0) p (QX i) (C i 0) (hQ ..); -- supply named
    · rw[←vert1 A T sym B hT F hf x Q hA]; exact he ..
    exact readS A T sym B hT F hf x Q hA i 0
    exact ht
    omega
    exact hC
    exact fun z=> by rw [pier A hA (Nat.zero_le _)]; exact Depth.first A 0 (Nat.zero_le _) _
lemma facet_two : ‖qv p Z1 (ηR w w) D i1 i2-ts x p V1 (ℓ w) w Q i1 i2‖ ≤ 4*KT:=by
    let f(i:Axis):= piv w i * ((l V1 (ℓ w)) (QX i)); have hp:(∑ i:Axis,f i)= ts x p V1 (ℓ w) w Q i1 i2:=by unfold f piv; simp[ite_mul]; rfl
    rw [←hp]; apply force1 A T sym B hT F hf x Q hA C he D hD P n m t a hQ p i1 i2; intro i; apply meanV w T i1 i2 i W' (cR i 0 0) p (QX i) (C i 0) (hQ ..); -- supply named
    · rw[←vert1 A T sym B hT F hf x Q hA]; exact he ..
    exact readS A T sym B hT F hf x Q hA i 0
    exact ht
    omega
    exact hC
    exact fun z=> by rw [pier A hA (Nat.zero_le _)]; exact Depth.first A 0 (Nat.zero_le _) _
lemma facet_ance(h:w≠u) : ‖qv p Z1 (ηR w u) D i1 i2 - (ts x p V1 (ℓ u) w Q i1 i2+ts x p V1 (ℓ w) u Q i1 i2)‖ ≤4*KT:=by
    let f(i:Axis):= piv w i* ((l V1 (ℓ u)) (QX i))+ piv u i*((l V1 (ℓ w)) (QX i)); have hp:(∑ i:Axis,f i)=ts x p V1 (ℓ u) w Q i1 i2+ ts x p V1 (ℓ w) u Q i1 i2:=by unfold f piv; simp_rw[ite_mul,sum_add_distrib,zero_mul,one_mul]; simp only[sum_ite_eq,mem_univ,if_true]; rfl
    rw [←hp]; apply force1 A T sym B hT F hf x Q hA C he D hD P n m t a hQ p i1 i2; intro i; apply meanP w u T i1 i2 i W' (cR i 0 0) p (QX i) (C i 0) (hQ ..) (by rw[←vert1 A T sym B hT F hf x Q hA]; exact he ..) (readS A T sym B hT F hf x Q hA i 0) ht (by omega) hC (fun z=> by rw [pier A hA (Nat.zero_le _)]; exact Depth.first A 0 (Nat.zero_le _) _) h
lemma facet_Δ : ‖qv p (Yp w) (Yp u) D i1 i2 - (ts x p V1 (ℓ u) w Q i1 i2+ts x p (ℓ w) V1 u Q i1 i2)‖ ≤4*KT:=by
    let f(i:Axis):= piv w i* ((l V1 (ℓ u)) (QX i))+ piv u i*((l (ℓ w) V1) (QX i)); have hp:(∑ i:Axis,f i)=ts x p V1 (ℓ u) w Q i1 i2+ ts x p (ℓ w) V1 u Q i1 i2:=by unfold f piv; simp_rw[ite_mul,sum_add_distrib,zero_mul,one_mul]; simp only[sum_ite_eq,mem_univ,if_true]; rfl
    rw [←hp]; apply force1 A T sym B hT F hf x Q hA C he D hD P n m t a hQ p i1 i2; intro i; apply meanD w u T i1 i2 i W' (cR i 0 0) p (QX i) (C i 0) (hQ ..) (by rw[←vert1 A T sym B hT F hf x Q hA]; exact he ..) (readS A T sym B hT F hf x Q hA i 0) ht (by omega) hC (fun z=> by rw [pier A hA (Nat.zero_le _)]; exact Depth.first A 0 (Nat.zero_le _) _)
lemma shells(w:Fin 6): ‖obV D p w i1 i2 - obS x Q p w i1 i2‖≤ 4*KT:=by
    fin_cases w
    · change ‖obV D p 0 i1 i2-obS x Q p 0 i1 i2‖ ≤ _; rw [show obV D p _= _ from ob_ve0 p D,show obS x Q p _= _ from ob_sn0 p x Q]; exact facet_lead A T sym B hT F hf x Q hA C he D hD P n m t a hm hC ht hQ p i1 i2 0
    · change ‖obV D p 1 i1 i2-obS x Q p 1 i1 i2‖ ≤ _; rw [show obV D p _= _ from ob_ve1 p D,show obS x Q p _= _ from ob_sn1 p x Q]; exact facet_lead A T sym B hT F hf x Q hA C he D hD P n m t a hm hC ht hQ p i1 i2 1
    · change ‖obV D p 2 i1 i2-obS x Q p 2 i1 i2‖ ≤ _; rw [show obV D p _= _ from ob_ve2 p D,show obS x Q p _= _ from ob_sn2 p x Q]; exact facet_two A T sym B hT F hf x Q hA C he D hD P n m t a hm hC ht hQ p i1 i2 0
    · change ‖obV D p 3 i1 i2-obS x Q p 3 i1 i2‖ ≤ _; rw [show obV D p _= _ from ob_ve3 p D,show obS x Q p _= _ from ob_sn3 p x Q]; exact facet_two A T sym B hT F hf x Q hA C he D hD P n m t a hm hC ht hQ p i1 i2 1
    · change ‖obV D p 4 i1 i2-obS x Q p 4 i1 i2‖ ≤ _; rw [show obV D p _= _ from ob_ve4 p D,show obS x Q p _= _ from ob_sn4 p x Q]; exact facet_ance A T sym B hT F hf x Q hA C he D hD P n m t a hm hC ht hQ p i1 i2 0 1 (by decide)
    · change ‖obV D p 5 i1 i2-obS x Q p 5 i1 i2‖ ≤ _; rw [show obV D p _= _ from ob_ve5 p D,show obS x Q p _= _ from ob_sn5 p x Q]; exact facet_Δ A T sym B hT F hf x Q hA C he D hD P n m t a hm hC ht hQ p i1 i2 1 0
end YM.Massive.Patria.Gall.Jewels
#print axioms YM.Massive.Patria.Gall.Jewels.shells
