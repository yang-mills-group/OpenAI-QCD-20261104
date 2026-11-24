import YM.Eole.Piles
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Bloc
variable (q:I→Bool)
local notation "X"=> Patio (A⊕Spine I)
local notation "Z"=> Patio (A⊕Spine J)
local notation "T'"=> spark -- dummy
local notation "p"=> glowT W g
local notation "Γ"=> W.plant
local notation "F"=> lane A q W
local notation "P"=> sparC A q W
local notation "u"=> W.flag q
variable (x:E⊕K→Patio (A⊕Spine I))(h:∀ i,Polite q (g i) (x i))
noncomputable abbrev reward (s:Finset (E⊕K)):= lane A q W (p s) (∏ i∈s,x i)
include h
lemma paint_packets (s:Finset (E⊕K)) : Polite q (bins g s) (∏ i∈s,x i):=by
    classical
    induction s using Finset.induction_on with | empty=> rw [bins,biUnion_empty,prod_empty]; exact polite_empty_one _|insert i s hi ih=> rw [bins,biUnion_insert,prod_insert hi]; exact (h i).attached ih
omit h
lemma plant_sum (t z:Finset J): W.plant (t∪z)=W.plant t∪W.plant z:=by ext x; simp only[mem_union,belongs]
lemma paintZ {D:Type}(m:D→ Finset J)(a:D→ X)(s:Finset D) (hh:∀ i∈s,Polite q (Γ (m i)) (a i)) : Polite q (Γ (s.biUnion m)) (∏ i∈s,a i):=by
    induction s using Finset.induction_on with
    | empty=> rw[biUnion_empty,show W.plant ∅=∅ from biUnion_empty,prod_empty]; exact polite_empty_one _
    | insert i s hi ih=> rw [prod_insert hi,biUnion_insert,plant_sum W]; exact (hh _ (mem_insert_self ..)).attached (ih fun t ht=>hh _ (mem_insert_of_mem ht))
include h
lemma spun (s:Finset (Finset (E⊕K)))(he:(s:Set (Finset N)).PairwiseDisjoint p) (hk:∀ i∈s,mural W g i) : lane A q W (s.biUnion p) (∏ i∈s,∏ j∈i,x j)= ∏ i∈s,reward W g q x i:=by -- order
    induction s using Finset.induction_on with
    | empty=> rw [biUnion_empty,prod_empty,prod_empty]; exact map_one (rootR (Spine I) A) ▸ map_one (rootR (Spine J) A) ▸ planted_value A q W 1
    | insert a s ha ih=>
          have hv(k)(hx:k∈s):k∈insert a s:=mem_insert_of_mem hx; have hD : Disjoint (p a) (s.biUnion p):= disjoint_left.mpr fun k ht hx=>by obtain ⟨b,hb,hx⟩:=mem_biUnion.mp hx; exact disjoint_left.mp (he (mem_insert_self ..) (hv _ hb) (by rintro rfl; exact ha hb)) ht hx
          rw [biUnion_insert,prod_insert ha,prod_insert ha]; rw[← ih (Set.PairwiseDisjoint.subset he (by simp)) (fun i hi=> hk _ (hv _ hi))]; apply ribs A q W _ _ hD _ _; exact (hk _ (mem_insert_self ..)).symm ▸ paint_packets g q x h a -- mural reducible field .symm?
          let r i:=∏ j∈i,x j; exact paintZ W q p _ _ fun i hi=> (hk _ (hv _ hi)).symm ▸ paint_packets g q x h i -- define
noncomputable def prize (s: Finset (E⊕K))(t:Support c):Z:= if selected Y s ∧ flagsOf Y s=t then sparC A q W (∏ i∈s,x i) else 0
noncomputable def wanted (s:Finset (Finset (E⊕K)))(t:Support c):Z:= if (∀ i∈s,approved W g Y i)∧ CPl Y s ∧ t =s.biUnion (flagsOf Y) then ∏ i∈s,reward W g q x i else 0
variable (t:Support c)
lemma unique_col (s:Finset (E⊕K)) : wanted W g Y q x (piles W g s) t = prize W Y q x s t:=by
    let r:=piles W g s; have hp:r.biUnion id=s:= recombine _ _; have hv:(r:Set (Finset N)).PairwiseDisjoint (glowT W g):=fun i hi j hj hn=> by
                have he:= Collide.separate (tags W g) s hi hj hn; change Disjoint (i.biUnion _) (j.biUnion _) at he; rw[tiles,tiles] at he; exact he
    have hk : flagsOf Y s= r.biUnion (flagsOf Y):= (congr_arg _ hp.symm).trans (coincidence ..)
    unfold prize wanted; split; next he=>
           have hQ := leap_parts Y r (fun i hi=> (he.1 i hi).2.2) he.2.1; rw[hp] at hQ; have hs(i)(h:i∈r):= (he.1 i h).2.1; have h_1:= full_parts W g r hs; rw [hp] at h_1; have h2 : Polite q (W.plant (p s)) (∏ i∈s,x i):=(show W.plant _= bins g _ from h_1).symm ▸ paint_packets g q x h s
           rw [if_pos ⟨hQ,hk.trans he.2.2.symm⟩,single_plant A q W _ h2]
           have h_z:=spun W g q x h _ hv hs; rw [squeeze,hp,show (∏ i∈r,∏ j∈i,x j)=∏ i∈r.biUnion id,x i from (prod_biUnion (f:=x) (erases (tags W g) s)).symm,hp] at h_z; exact h_z.symm
    next he=>by_cases hg:selected Y s∧ flagsOf Y s=t; swap; · rw[if_neg hg]
             rw [if_pos hg]; apply Eq.symm; apply all_seed A q W (bins g s) _ (paint_packets g q x h s); intro h_m; have hf:= beaten W g Y s hg.1; exact he ⟨fun i hX=>⟨(living (tags W g) hX).2,liberties W g s h_m i hX,hf.1 i hX⟩,hf.2,hg.2.symm.trans hk⟩
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.unique_col
