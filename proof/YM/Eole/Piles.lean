import YM.Eole.Omega
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
abbrev bins (s:Finset (E⊕K)):= s.biUnion g
abbrev glowT (s:Finset (E⊕K)):= W.core (bins g s)
abbrev tags (i:E⊕K):= W.core (g i)
lemma tiles (s:Finset N): s.biUnion (tags W g)=glowT W g s:=by ext x; simp only[bins,tags,glowT,Bloc.core,mem_biUnion,mem_image]; aesop
abbrev piles (s:Finset (E⊕K)) : Finset (Finset (E⊕K)):= parts (tags W g) s
def mural (s:Finset (E⊕K)) : Prop:= W.plant (glowT W g s)=bins g s
abbrev selected (s:Finset (E⊕K)) : Prop:= (↑s.toRight : Set K).PairwiseDisjoint (fun i=>(Y i).place)
abbrev approved (s:Finset (E⊕K)) : Prop:= spark (tags W g) s ∧ mural W g s ∧ selected Y s
abbrev dimK (s:Finset (E⊕K)):Support c:= s.toRight.biUnion (fun i=>(Y i).place)
abbrev flagsOf (s:Finset (E⊕K)):Support c:= s.toRight.biUnion (fun i=>(Y i).inv)
lemma liberties (s:Finset (E⊕K)) (h:mural W g s)(d:Finset N) (H:d∈ piles W g s): mural W g d:=by -- syntax binder edit
   unfold mural; refine Finset.ext fun i=> ?_; rw [W.belongs]; constructor
   · intro hp; rw [←tiles W g d] at hp; let r:=piles W g s; have hv:=Collide.separate (tags W g) s; obtain ⟨k,hk,hv'⟩:=mem_biUnion.mp hp; have hr:=mem_image.mp (show W.unit_ i∈(g k).image W.unit_ from hv'); obtain ⟨j,hj,ht⟩:=hr; have hk':= (living (tags W g) H).1 hk -- edit H name
     have hM:W.unit_ i∈ glowT W g s:=mem_image.mpr ⟨j,mem_biUnion.mpr ⟨k,hk',hj⟩,ht⟩; obtain ⟨p,hp,hP⟩:= mem_biUnion.mp (h ▸ ((W.belongs ..).2 hM)); let v:=core (tags W g) s p
     have hg:v ∈r:= mem_image_of_mem _ hp; have hq:p ∈v:= (aglow (tags W g)).2 ⟨hp,.refl⟩; have he: W.unit_ i∈ tags W g p:=mem_image.mpr ⟨i,hP,rfl⟩
     by_cases hw:d=v; · exact mem_biUnion.mpr ⟨p,hw.symm ▸ hq,hP⟩
     exact False.elim (disjoint_left.mp (hv H hg hw) (mem_biUnion.mpr ⟨k,hk,hv'⟩) (mem_biUnion.mpr ⟨p,hq,he⟩)) -- hv' consumed
   intro hx; exact mem_image.mpr ⟨i,hx,rfl⟩
lemma parts_sums {D:Type}(g:E⊕K→Finset D)(u:Finset (Finset N)): (u.biUnion id).biUnion g=u.biUnion fun i=>i.biUnion g:=by ext x; simp only[mem_biUnion,id]; aesop
lemma cop_right (u:Finset (Finset N)) : (u.biUnion id).toRight=u.biUnion (fun i=>i.toRight):=by ext x; simp only [mem_toRight,mem_biUnion,id]
lemma coincidence (u:Finset (Finset N)) : (flagsOf Y (u.biUnion id))=u.biUnion fun i=> flagsOf Y i:=by ext x; simp only [flagsOf,mem_biUnion,mem_toRight,id]; aesop
lemma squeeze (u:Finset (Finset N)): u.biUnion (glowT W g) = glowT W g (u.biUnion id):=by ext x; simp only [glowT,bins,Bloc.core,mem_biUnion,id,mem_image]; aesop
lemma full_parts (s:Finset (Finset N))(hv:∀ i∈s,mural W g i): mural W g (s.biUnion id):=by
    unfold mural; rw [←squeeze,bins,parts_sums]; ext x; simp only [mem_biUnion,W.belongs]; exact exists_congr fun j=>and_congr_right (fun h=> by rw [← Finset.mem_biUnion]; change _ ↔ x∈bins g j; rw[← (show _ = bins g j from hv j h),W.belongs]) -- exists_prop argument
-- part cross selected. Need prove given disjoint original K wall across outputs always selected.
abbrev CPl (s:Finset (Finset (E⊕K))):Prop:= (s:Set (Finset (E⊕K))).PairwiseDisjoint (dimK Y)
lemma leap_parts (u:Finset (Finset N))(hv:∀ i∈u,selected Y i)(hX:CPl Y u) : selected Y (u.biUnion id):=by
    intro i hi k hk he
    rw[mem_coe,cop_right] at hi hk; obtain ⟨p,hp,h⟩:= mem_biUnion.mp hi; obtain ⟨q,hq,h'⟩:=mem_biUnion.mp hk; by_cases hn:p=q; · subst q; exact hv p hp h h' he
    exact Disjoint.mono (subset_biUnion_of_mem (fun k=> (Y k).place) h) (subset_biUnion_of_mem (fun k=> (Y k).place) h') (hX hp hq hn)
lemma beaten (s:Finset (E⊕K)) (ht:selected Y s) : (∀ i∈ piles W g s,selected Y i) ∧ CPl Y (piles W g s):=by
    have hh:=erases (tags W g) s; let r:=piles W g s; have hz {x:Finset N}(hp:x∈r) : x.toRight⊆ s.toRight:= fun i hi=> mem_toRight.mpr ((living _ hp).1 (mem_toRight.mp hi)); refine ⟨fun i hi p hp q hq he=>ht (hz hi hp) (hz hi hq) he, fun p hp q hq he=>disjoint_left.mpr ?_⟩
    intro x hx hu; obtain ⟨i,hi,hx⟩:=mem_biUnion.mp hx; obtain ⟨j,hj,hu⟩:=mem_biUnion.mp hu; by_cases h:i=j; · subst i; exact disjoint_left.mp (hh hp hq he) (mem_toRight.mp hi) (mem_toRight.mp hj)
    exact disjoint_left.mp (ht (hz hp hi) (hz hq hj) h) hx hu -- ht implicit args
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.beaten
