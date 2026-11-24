import YM.Arise.Sun
import YM.Vest.Corn
/-! # moment algebra crop at touch. initialize with self-rates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Count
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Massive UV UV.Free QCD QCD.Grass QCD.Bera QCD.Cove QCD.Anomaly QCD.Creek Count Vest
open MassiveQCD.Sample.Quills
open MassiveQCD.Ribbon
open YM.Arise.Range YM.Arise.Bill
open MassiveQCD.Play MassiveQCD.Play.Chamber
variable {n m i j d k:ℕ}
variable {I X Y B A C F D:Type}[Fintype I][Fintype X][Fintype Y][Fintype A][Fintype B][Fintype C][Fintype F][Fintype D]
section
variable {P R:Type}[CommRing R]
-- singleton cores.T at unit and marker budgets
noncomputable def milk (F:P→R)(v:Finset P):R := if h:v.card=1 then (F (Classical.choose (card_eq_one.1 h))) else 0
@[simp] lemma milk1(F:P→R)(x:P):milk F {x}=F x:=by
   unfold milk; split; next h=> apply congr_arg; exact Finset.singleton_injective (Classical.choose_spec (card_eq_one.1 h)).symm
   next h=>simp_all
lemma partyR (F:I→R) (v:Finset I) : parties (milk F) v=∏ i∈ v,F i:=by
    let w:=fun i:I=> ({i}:Finset I); let P:=v.image w; have hp (j:Finset I) : j∈P↔∃ i∈v,j=w i:=by unfold P; rw [mem_image]; exact exists_congr fun i=>and_congr Iff.rfl eq_comm -- and.intro
    have hv:P ∈ registry v:=by
        refine mem_filter.mpr ⟨mem_powerset.mpr ?_,?_,?_,?_⟩
        · intro i hi; obtain ⟨j,hj,rfl⟩:= (hp i).mp hi; exact mem_powerset.mpr (singleton_subset_iff.mpr hj)
        · intro h; obtain ⟨j,hj,h⟩:= (hp _).mp h; exact (Finset.singleton_nonempty j).ne_empty h.symm
        · ext p; rw [mem_biUnion]; constructor; rintro ⟨x,hx,h⟩; obtain ⟨j,hj,rfl⟩:=(hp _).mp hx; exact (mem_singleton.mp h).symm ▸ hj
          intro h; exact ⟨_,mem_image_of_mem w h, Finset.mem_singleton_self p⟩
        intro i hi j hj hij; obtain ⟨k,hk,rfl⟩:=(hp i).mp hi; obtain ⟨k',hk',rfl⟩:=(hp j).mp hj; exact Finset.disjoint_singleton.mpr (fun he=> hij (congr_arg w he))
    unfold parties; rw [sum_eq_single_of_mem P hv]; unfold P w; rw [Finset.prod_image Finset.singleton_injective.injOn]; simp
    intro i hi h; by_cases ht:∀ j∈i,j.card=1
    · obtain ⟨_,hZ,hL,H⟩:=mem_filter.mp hi; apply False.elim (h (?_)); ext j; rw [hp]; constructor
      · intro hj; obtain ⟨p,hp⟩:=card_eq_one.1 (ht j hj); exact ⟨p,(member hi hj).2 (hp.symm ▸ Finset.mem_singleton_self p),hp⟩
      rintro ⟨p,hp,rfl⟩; rw [← hL] at hp; obtain ⟨j,hj,h₀⟩:=mem_biUnion.mp hp; obtain ⟨u,rfl⟩:=card_eq_one.1 (ht j hj); rw [mem_singleton.mp h₀]; exact hj
    push Not at ht; obtain ⟨j,hj,h⟩:=ht; exact prod_eq_zero hj (dif_neg h)
end
open MassiveQCD.FlareV
section Roll
local notation "Vb"=> Papers A (Patio X)
local notation "Vc"=> Papers B (Patio Y)
local notation "V₀"=> Papers C (Patio D)
variable (T: Tone A X B Y)(S:Tone B Y C D)
noncomputable def pivotV (P:I→Papers A (Patio X))(w:I→ℝ) : Finset I→ Papers B (Patio Y):= milk (fun i=>(w i:ℂ) • T.read (P i))
variable (P:I→ Papers A (Patio X))(w:I→ℝ)
variable {Q:Finset I}(m:I→ Finset X)(e:I→ Finset A)
variable (ht:∀ i∈ Q,P i∈ Ledger (m i) (e i) n j)(hp :∀ i∈Q,∀ k∈ Q, i ≠ k → Disjoint (m i) (m k)∧(∀ a∈m i,∀ b∈ m k,T.V a b=0) ∧ ∀ a∈e i,∀ b∈ e k,T.Q.cov a b=0)
include ht hp
lemma weightedN (v: Finset I)(h:v ⊆ Q): parties (pivotV T P w) v=MassiveQCD.FlareV.give w v • T.read (∏ i∈ v,P i):=by
    unfold pivotV; rw [partyR]; induction v using Finset.induction_on with
    | empty=> rw [show T.read (∏ i∈∅,P i) =1 from (by rw [prod_empty]; exact Tone.noneW _), prod_empty]; simp [MassiveQCD.FlareV.give]
    | insert p b hd ih=>
       let X':=b.biUnion m; let Y':=b.biUnion e; have hb:= (Finset.subset_insert ..).trans h
       -- ambiguity
       have hp':p∈ Q :=h (mem_insert_self ..)
       have h0(v:Finset I)(hv:v⊆ b):(∏ i∈v,P i)∈ Ledger X' Y' (v.card*n) (v.card*j):=by
           induction v using Finset.induction_on with
           | empty=>rw [prod_empty]; exact arrives _
           | insert i v hi ih=> have hi':i∈b:=hv (mem_insert_self ..); rw [Finset.prod_insert hi,card_insert_of_notMem hi,Nat.add_comm, Nat.add_mul,Nat.add_mul, one_mul,one_mul]; exact harbored (leaguer (ht i (hb hi')) (Finset.subset_biUnion_of_mem m hi') (Finset.subset_biUnion_of_mem e hi') le_rfl le_rfl) (ih ((subset_insert ..).trans hv))
       have hW(i)(hv:i∈ b): p ≠ i:= fun hh=>hd (hh.symm ▸ hv); have he:Disjoint (m p) X':= by apply disjoint_left.mpr; intro i hi hj; obtain ⟨k,hk,hj⟩:=mem_biUnion.mp hj; exact Finset.disjoint_left.mp (hp p hp' k (hb hk) (hW k hk)).1 hi hj
       have hg: T.read (P p*∏ i∈b,P i)=T.read (P p)*T.read (∏ i∈b,P i):=by
           apply siloes (hp:=ht _ hp') (hf:=h0 b (Finset.Subset.refl _)) (hh:=he); intro i hi j hj; obtain ⟨k,hk,hj⟩:= mem_biUnion.mp hj; exact ⟨(hp p hp' k (hb hk) (hW k hk)).2.1 i hi j hj,(hp k (hb hk) p hp' (hW _ hk).symm).2.1 j hj i hi⟩
           intro i hi j hj; obtain ⟨k,hk,hj⟩:=mem_biUnion.mp hj; exact (hp p hp' k (hb hk) (hW _ hk)).2.2 i hi j hj
       rw [Finset.prod_insert hd,Finset.prod_insert hd,hg,ih hb]; unfold give; rw [Finset.prod_insert hd,_root_.smul_mul_assoc, _root_.mul_smul_comm,smul_smul]
lemma lends (v:Finset I)(h:v ⊆ Q): S.read (parties (pivotV T P w) v)=MassiveQCD.FlareV.give w v • (T.after S).read (∏ i∈v,P i):=by rw [weightedN T P w m e ht hp v h,Tone.spoke,map_smul]
end Roll
end YM.Arise.Count
#print axioms YM.Arise.Count.lends
