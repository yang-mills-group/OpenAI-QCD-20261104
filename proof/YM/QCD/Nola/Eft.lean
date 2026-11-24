import YM.QCD.Nola.Stars
import YM.QCD.Cove.Drip
import YM.QCD.Gas.Froof
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι K κ A:Type*} {n : Side} {k:ℕ} [Fintype A]
structure Pads (p:A→Site n)(ι κ : Type*) where
    source : ι→ Patio A
    buys: κ→ EndA A
    commute i j : Commute (buys i) (buys j)
    leaves: ι⊕κ→ Support n
    budget (i:ι):light A (source i) ∈region (univ.filter fun i' => p i'∈ leaves (.inl i))
    bill (i:κ): Creek.Stays (buys i) (univ.filter fun i'=>p i'∈leaves (.inr i))
variable {p:A→Site n}(S:Pads p ι κ)
namespace Pads
abbrev Stamp (s: Finset (ι⊕ κ)):=s.biUnion S.leaves
def alphabet (s: Support n) := univ.filter (fun i=>p i∈s)
def grape (u: Finset ι): Patio A:=∏ i∈u,S.source i
def ping (u: Finset κ):= u.noncommProd S.buys (fun i _ j _ _=> S.commute ..)
def oust (u:Finset (ι⊕κ)):= S.ping u.toRight (light A (S.grape u.toLeft))
private lemma orthoF (s:Finset (ι⊕κ))(i: ι⊕κ)(h:i∈s): alphabet (p:=p) (S.leaves i)⊆ alphabet (p:=p) (S.Stamp s):= fun j hj=> mem_filter.mpr ⟨mem_univ _, (subset_biUnion_of_mem _ h) (mem_filter.mp hj).2⟩
lemma swell (s: Finset (ι ⊕ κ)): light A (S.grape s.toLeft) ∈ region (alphabet (p:=p) (S.Stamp s)):=by
    let X:= region (alphabet (p:=p) (S.Stamp s)); have H (u:Finset ι)(h:u⊆s.toLeft): light A (S.grape u)∈ X:=by
          induction u using Finset.induction_on with
          | empty=> rw [grape,prod_empty,map_one]; exact X.one_mem
          | insert a s' hi he=> rw [grape,prod_insert hi,map_mul]; exact X.mul_mem (regionMon (S.orthoF _ (.inl a) (mem_toLeft.mp (h (mem_insert_self ..)))) (S.budget a)) (he ((subset_insert ..).trans h))
    exact H _ (Finset.Subset.refl _)
lemma rocky (s: Finset (ι⊕κ)): Stays (S.ping s.toRight) (alphabet (p:=p) (S.Stamp s)):= by
    exact Finset.noncommProd_induction s.toRight S.buys _ (fun F=> Stays F (alphabet (p:=p) (S.Stamp s))) (fun _ _ he ht=> Stays.paysM he ht) (Stays.paidI _) (fun i hi=> Stays.heel (S.bill i) (S.orthoF s (.inr i) (mem_toRight.mp hi))) -- sig
lemma shire (s:Finset (ι⊕κ)): Grass.Plus (S.oust s) ∧ S.oust s ∈ region (alphabet (p:=p) (S.Stamp s)):= ⟨(rocky S s).evenPay (bright _), (rocky S s).keeps (Finset.Subset.refl _) _ (swell S s)⟩
def ham (s:Finset (ι⊕κ)): Patio A:=⟨S.oust s,(shire S s).1⟩
lemma peek (s:Finset (ι⊕κ)):light A (S.ham s)=S.oust s:=rfl
lemma ping_step (u v:Finset κ)(h:Disjoint u v): S.ping (u∪v)=S.ping u*S.ping v:=by
     induction u using Finset.induction_on with
     | empty=>simp [ping]
     | insert i u he ih=> rw [insert_union, ping, noncommProd_insert_of_notMem _ _ _ _ (fun hx=> (mem_union.mp hx).elim he (fun H=> Finset.disjoint_left.mp h (mem_insert_self ..) H)), show S.ping (insert i u)=_ from (show S.ping _= S.buys i * S.ping u from noncommProd_insert_of_notMem _ _ _ _ he)]; change _ * S.ping _= _; rw [ih (h.mono_left (subset_insert ..)),mul_assoc]
 
lemma ham_union (u v:Finset (ι⊕κ))(h:Disjoint u v)(hh:Disjoint (S.Stamp u) (S.Stamp v)):S.ham (u∪v)= S.ham u*S.ham v:=by
     let A1:= alphabet (p:=p) (S.Stamp u); let A2:= alphabet (p:=p) (S.Stamp v); have hx:Disjoint A1 A2:= Finset.disjoint_left.mpr fun i hi hi'=> Finset.disjoint_left.mp hh (mem_filter.mp hi).2 (mem_filter.mp hi').2
     apply Subtype.ext; change S.oust _=S.oust _*S.oust _; unfold oust; rw [Finset.toLeft_union,Finset.toRight_union,S.ping_step _ _ (Finset.disjoint_left.mpr fun i hi hi'=> Finset.disjoint_left.mp h (mem_toRight.mp hi) (mem_toRight.mp hi')), grape, prod_union (Finset.disjoint_left.mpr fun i hi hi'=> Finset.disjoint_left.mp h (mem_toLeft.mp hi) (mem_toLeft.mp hi')),map_mul]; exact Stays.paysR (S.rocky u) (S.rocky v) hx (swell S u) (swell S v) (bright _) (bright _)
end Pads
end YM.QCD.Nola
