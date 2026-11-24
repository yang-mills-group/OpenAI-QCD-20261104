import YM.QCD.Cove.Wave
import Mathlib.Data.Finset.NoncommProd
/-! # explicit optional expansion -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek NormedSpace Finset Ledge
open scoped BigOperators Topology ContDiff Classical
variable {D:Type*} {A:Type*}[Fintype A]

lemma sprinkle {Q:Type*}[AddCommMonoid Q] (p:Finset D)(i:D)(h:i∉p)(B:Finset D→Q): ∑ k ∈ (insert i p).powerset,B k=∑ k ∈ p.powerset,B k+∑ k∈p.powerset,B (insert i k):=by
  rw [powerset_insert,sum_union,sum_image]
  · rintro x hx y hy he
    calc x= (insert i x).erase i:=by rw [erase_insert (fun he'=>h ((mem_powerset.mp hx) he')) ]
         _ = y:=by rw [he,erase_insert (fun he'=> h ((mem_powerset.mp hy) he'))] -- syntax
  rw [Finset.disjoint_left]; intro k hk he; obtain ⟨q,hq,rfl⟩:= mem_image.mp he; exact h ((mem_powerset.mp hk) (mem_insert_self ..))

lemma dripe (X : D→ EndA A)(hv: ∀ i j,Commute (X i) (X j))(s : Finset D): ∑ k∈s.powerset, k.noncommProd (fun i=> excess (X i)) (by
    intro i a j b he; exact ((Commute.symm (roundP (roundP (hv j i).symm).symm)).sub_left (by exact Commute.one_left _)).sub_right (Commute.one_right _)) = birth (∑ i∈s,X i):=by
  letI : NormedAlgebra ℚ (EndA A):=.restrictScalars ℚ ℂ _
  induction s using Finset.induction_on with
  | empty=> simp only [powerset_empty,sum_singleton,noncommProd_empty,sum_empty]; exact (NormedSpace.exp_zero).symm
  | insert i s hi ih=>
    rw [sprinkle s i hi,sum_insert hi]; rw [ih]
    rw [show birth (X i+∑ j∈s,X j)=birth (X i)*birth (∑ j∈s,X j) from NormedSpace.exp_add_of_commute (finiteComm s X fun j _=> hv i j)]
    suffices (∑ k∈ s.powerset,(insert i k).noncommProd (fun i=> excess (X i)) (by
      intro i a j b he; exact ((Commute.symm (roundP (roundP (hv j i).symm).symm)).sub_left (by exact Commute.one_left _)).sub_right (Commute.one_right _)))= excess (X i) *birth (∑ j∈s,X j) by rw [this]; rw [excess,sub_mul,one_mul,add_sub_cancel ..]
    rw [←ih,mul_sum]
    apply sum_congr rfl; intro k hk
    rw [noncommProd_insert_of_notMem k i _ _ (fun he=> hi ((mem_powerset.mp hk) he))]

lemma flicker (G:D→Patio A)(s : Finset D): exp (∑ i∈s,G i)=∑ k∈s.powerset, ∏ j∈k,(exp (G j)-1):=by
  induction s using Finset.induction_on with
  | empty=> simp
  | insert i s hi ih=>
    rw [sprinkle s i hi,sum_insert hi,exp_add]; rw [← ih]
    have h : ∑ k ∈ s.powerset, ∏ j∈insert i k,(exp (G j)-1)= (exp (G i)-1)*exp (∑ i∈s,G i):=by
      rw [ih,mul_sum]; exact sum_congr rfl (fun k hk=> prod_insert (fun he=>hi ((mem_powerset.mp hk) he)))
    rw [h]; ring
end YM.QCD.Cove
