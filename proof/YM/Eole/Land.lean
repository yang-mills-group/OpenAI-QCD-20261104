import YM.Eole.Lumens
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
-- legal outputs
abbrev Cand : Type:= {s:Finset (E⊕K)// approved W g Y s ∧ ¬ s.toRight.Nonempty}
abbrev Hard : Type:= {s:Finset (E⊕K)// approved W g Y s∧ s.toRight.Nonempty}
local notation "C"=> Cand W g Y
local notation "D"=> Hard W g Y
noncomputable def shiftπ : (Cand W g Y ⊕ Hard W g Y) ↪ Finset (E⊕K):=⟨fun i=>Sum.elim Subtype.val Subtype.val i, fun a b=> by
    rcases a with a|a <;>rcases b with b|b <;> intro h <;> change a.val=b.val at h
    · exact congr_arg _ (Subtype.ext h)
    · exact False.elim (a.2.2 (h.symm ▸ b.2.2))
    · exact False.elim (b.2.2 (h ▸ a.2.2))
    exact congr_arg _ (Subtype.ext h)⟩
noncomputable def hats (s:Hard W g Y) : Hat c:= ⟨dimK Y s.val, flagsOf Y s.val,(by obtain ⟨i,h⟩:=s.2.2; exact (Y i).alive.mono (subset_biUnion_of_mem (fun i=>(Y i).inv) h)),fun i hp=>by obtain ⟨j,hp,he⟩:=mem_biUnion.mp hp; exact mem_biUnion.mpr ⟨j,hp,(Y j).part he⟩⟩
lemma prized (s:C⊕D) : approved W g Y (shiftπ W g Y s):=by cases s with| inl s=>exact s.2.1| inr s=>exact s.2.1 -- edit
lemma emitted (s:Finset (E⊕K))(h:approved W g Y s): s∈ Set.range (shiftπ W g Y):=by by_cases he:s.toRight.Nonempty; exact ⟨Sum.inr ⟨s,h,he⟩,rfl⟩; exact ⟨Sum.inl ⟨s,h,he⟩,rfl⟩
lemma empty_dim (i:C): dimK Y i.val=∅∧ flagsOf Y i.val=∅:=by unfold dimK flagsOf; rw [Finset.not_nonempty_iff_eq_empty.mp i.2.2]; simp
variable (a:Finset (Cand W g Y))(b:Finset (Hard W g Y))
local notation "π"=>shiftπ W g Y
local notation "Z"=> hats W g Y
noncomputable abbrev docket (W:Bloc I J) (g:E⊕K→Finset I) (Y:K→Hat c)(a:Finset (Cand W g Y))(b:Finset (Hard W g Y)):= (a.disjSum b).map (shiftπ W g Y)
lemma seed_set {i:Finset N}: i∈docket W g Y a b ↔ (∃ k:C, k∈a ∧ i=k.val)∨(∃ k:D,k∈b ∧ i=k.val):=by
   rw [docket,Finset.mem_map]; constructor
   · rintro ⟨(k|k),hh,rfl⟩; exact .inl ⟨k,(inl_mem_disjSum).1 hh,rfl⟩; exact .inr ⟨k,inr_mem_disjSum.mp hh,rfl⟩
   rintro (⟨k,h,rfl⟩|⟨k,h,rfl⟩); exact ⟨Sum.inl k,inl_mem_disjSum.mpr h,rfl⟩; exact ⟨Sum.inr k,inr_mem_disjSum.mpr h,rfl⟩
local notation "S"=>docket W g Y a b
lemma boundary : CPl Y (docket W g Y a b) ↔ (b:Set D).PairwiseDisjoint (fun i=>(Z i).place):=by
    constructor; intro h i hp j ht he; exact h (mem_map_of_mem π (inr_mem_disjSum.mpr hp)) (mem_map_of_mem π (inr_mem_disjSum.mpr ht)) ((π).injective.ne (Sum.inr_injective.ne he)) -- args hp inference fail
    intro h i hp j ht he; rcases (seed_set W g Y a b).mp hp with ⟨k,hk,rfl⟩|⟨k,hk,rfl⟩; change Disjoint _ _; rw[(empty_dim W g Y k).1]; exact disjoint_empty_left _
    rcases (seed_set W g Y a b).mp ht with ⟨m,hm,rfl⟩|⟨m,hm,rfl⟩; change Disjoint _ _; rw [(empty_dim W g Y m).1]; exact disjoint_empty_right _
    exact h hk hm fun h=>he (congr_arg _ h)
lemma zoneH : (docket W g Y a b).biUnion (flagsOf Y)=b.biUnion (fun i=>(Z i).inv):=by
    ext x; constructor; · intro h; obtain ⟨i,h,hx⟩:=mem_biUnion.mp h; rcases (seed_set W g Y a b).mp h with ⟨k,hk,rfl⟩|⟨k,hk,rfl⟩; rw [(empty_dim W g Y k).2] at hx; exact False.elim (notMem_empty _ hx); exact mem_biUnion.mpr ⟨k,hk,hx⟩
    intro h; obtain ⟨i,h,hx⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨i.val,(seed_set ..).mpr (Or.inr ⟨i,h,rfl⟩),hx⟩
variable (q:I→Bool) (x:E⊕K→Patio (A⊕Spine I))(t:Support c)
noncomputable abbrev softπ (i:C):=reward W g q x i.val
noncomputable abbrev hardπ (i:D):=reward W g q x i.val
lemma born_heads : wanted W g Y q x S t =(∏ i∈a,softπ W g Y q x i)*gift (hardπ W g Y q x) Z t b:=by
    unfold wanted gift; have h:∀ i∈S,approved W g Y i:=fun i h=>by obtain ⟨p,h,rfl⟩:= Finset.mem_map.mp h; exact prized ..
    rw[zoneH, boundary]; split_ifs with hv hh hh; · rw[docket,prod_map,prod_disjSum]; rfl
    · exact (hh hv.2).elim
    · exact (hv ⟨h,hh⟩).elim
    rw[mul_zero]
variable (h:∀ i,Polite q (g i) (x i))(hr:∀ i:E,(g (.inl i)).Nonempty)(hx: Summable fun i:E⊕K=> ‖x i‖)
local notation "Wq"=> W.flag q
include hr
lemma lightD (i:C) : (glowT W g i.val).Nonempty:=by
    obtain ⟨j,hp⟩:= i.2.1.1.1; cases j with
    | inl j=> exact ((hr j).mono (subset_biUnion_of_mem g hp)).image W.unit_
    | inr j=> exact False.elim (i.2.2 ⟨j,mem_toRight.mpr hp⟩)
local notation "Q"=> Bloc.sparC A q W
include h hx
set_option maxHeartbeats 600000 in
lemma paradigm (hQ:Summable fun i=> ‖softπ W g Y q x i‖)(hZ:Summable fun i=> ‖hardπ W g Y q x i‖): NormedSpace.exp (∑' i,softπ W g Y q x i)*(∑' i,gift (hardπ W g Y q x) Z t i)=Q (NormedSpace.exp (∑' i,x (.inl i))*(∑' i,gift (x ∘ Sum.inr) Y t i)):=by
    let v:= hardπ W g Y q x; let y:=softπ W g Y q x; let b:=gift v Z t; let γ (i:Finset C×Finset D):= (∏ j∈i.1,y j)* b i.2; let η:= (@Finset.sumEquiv C D).toEquiv; let χ:=fun i:Finset (C ⊕ D)=>i.map π
    have hv :∃ z,HasSum γ z ∧ z=NormedSpace.exp (∑' i,y i)*(∑' i,b i) := by
        have hN:=budgets Z t v hZ; have ht(i:C): y i*y i=0:=by let H:=glowT W g i.val; have hx : Polite (W.flag q) H (y i):=Bloc.overlay ..; exact hx.nilpotent hx (fun hg=>by obtain ⟨k,h⟩:=lightD W g Y hr i; exact disjoint_left.mp hg h h)
        let S₀:=NormedSpace.exp (∑' i,y i); refine ⟨S₀*∑' i,b i,?_ ,rfl⟩; exact Cove.toss_big (p:=b) (f:=fun i:Finset C=>∏ j∈i,y j) (illum y ht hQ) hN.of_norm.hasSum (illum y ht hQ).summable.norm hN
    let j (i:Finset (Finset (E⊕K))):=wanted W g Y q x i t; have hi:=developed W g Y q x h t hr hx; have hp:Injective χ:=map_injective ..
    have hM:=hp.hasSum_iff (f:=j) (fun i hi=> ?_ ) |>.mpr hi -- hi shadow.lacks
    · obtain ⟨z,k,hq⟩:=hv; have hz1(i): γ i=((j ∘ χ) ∘ η.symm) i:=by rcases i with ⟨a,b'⟩; exact (born_heads W g Y a b' q x t).symm
      exact hq ▸ k.unique (((η.symm.hasSum_iff).2 hM).congr_fun hz1)
    unfold j wanted; rw [if_neg]; intro hw; apply hi; let u':=i.preimage π (Embedding.injective π).injOn; refine ⟨u',?_⟩; ext s; constructor; · intro p; obtain ⟨d,h,rfl⟩:=Finset.mem_map.mp p; exact mem_preimage.mp h
    intro p; obtain ⟨j,rfl⟩:= emitted W g Y s (hw.1 s p); exact Finset.mem_map.mpr ⟨j,mem_preimage.mpr p,rfl⟩
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.paradigm
