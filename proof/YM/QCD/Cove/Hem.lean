import YM.QCD.Cove.Helix
/-! # No independence of coincident atoms. Exact gas stamps. Products collapsed. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send Fj
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{f c: Side}{S: Ratio c f}{E D J: Type}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "I"=> Fj D E J
variable (g:Send S F D) (P:Rise f F E J)(t:ℝ)
variable {M:Fj D E J→ Support c} (h: Count g P M)
include h
lemma spares {s w : Finset I} (hp:Disjoint (s.biUnion M) (w.biUnion M)) : P.spare (spent (s∪w)) ↔ P.spare (spent s)∧P.spare (spent w) := by
  have hw: spent (s∪w)=spent s∪spent w:=by ext; simp [spent]
  unfold Rise.spare; rw [hw,Finset.coe_union]; refine ⟨fun H=>⟨H.mono Set.subset_union_left,H.mono Set.subset_union_right⟩,?_⟩
  rintro ⟨h1,h2⟩ i hi j hj hh
  have ht (s:Finset I)(i:J)(hp:i∈spent s): (P.front i).place⊆brimW g P s:= fun j hj=> (native_sub g P s) (mem_biUnion.mpr ⟨Sum.inr (Sum.inr i),by simpa [spent] using hp,hj⟩)
  cases hi <;> cases hj <;> rename_i he hk
  · exact h1 he hk hh
  · exact Disjoint.mono (ht _ i he) (ht _ j hk) (remote g P h hp)
  · exact Disjoint.mono (ht _ _ he) (ht _ _ hk) (remote g P h hp).symm
  exact h2 he hk hh

omit h


def closeS (s:Finset I)(U:Grid f):Prop:= P.wish (spent s)=flags t U∩brimW g P s
def hue (s: Finset I)(U : Grid f) : EvenA c F:= if P.spare (spent s) ∧ closeS g P t s U then dye g P t s U else 0

include h
lemma close_join {s w: Finset I}(U:Grid f)(hp:Disjoint (s.biUnion M) (w.biUnion M)): closeS g P t (s∪w) U ↔ closeS g P t s U ∧ closeS g P t w U:=by
  have hw: spent (s∪w)=spent s∪spent w:=by ext; simp [spent]
  have he:P.wish (spent (s∪w))= P.wish (spent s)∪P.wish (spent w) := by rw [hw]; unfold Rise.wish; rw [union_biUnion]
  unfold closeS; rw [he,show brimW g P (s∪w)=brimW g P s∪brimW g P w by unfold brimW; rw [union_biUnion],inter_union_distrib_left]
  have hi (s:Finset I): P.wish (spent s)⊆brimW g P s:= Subset.trans (wish_sub g P s) (native_sub g P s)
  have hm : Disjoint (brimW g P s) (brimW g P w) := remote g P h hp
  constructor
  · intro hx; constructor
    · ext i; have hu:=Finset.ext_iff.mp hx i; simp only [mem_union,mem_inter] at *; constructor
      · intro hz; rcases hu.mp (.inl hz) with ht|ht; · exact ht
        exact False.elim (Finset.disjoint_left.mp hm (hi s hz) ht.2)
      intro hz; rcases hu.mpr (.inl hz) with ht|ht; · exact ht
      exact False.elim (Finset.disjoint_left.mp hm hz.2 (hi w ht))
    ext i; have hu:=Finset.ext_iff.mp hx i; simp only [mem_union,mem_inter] at *; constructor
    · intro hz; rcases hu.mp (.inr hz) with ht|ht; · exact False.elim (Finset.disjoint_left.mp hm ht.2 (hi w hz))
      exact ht
    intro hz; rcases hu.mpr (.inr hz) with ht|ht; · exact False.elim (Finset.disjoint_left.mp hm (hi s ht) hz.2)
    exact ht
  rintro ⟨h,h'⟩; rw [h,h']
lemma hue_join {U:Grid f}(ht:P.Wave t){s w:Finset I}(hp:Disjoint s w)(he:Disjoint (s.biUnion M) (w.biUnion M)): hue g P t (s∪w) U=hue g P t s U*hue g P t w U:=by
   by_cases hi:P.spare (spent s)<;>by_cases hx:P.spare (spent w)<;>by_cases hv:closeS g P t s U <;> by_cases hq:closeS g P t w U <;> simp [hue,close_join g P t h U he,spares g P h he, hi,hx,hv,hq,dye_join g P h U t ht hp he]
omit h
lemma hue_origin (U:Grid f): hue g P t ∅ U=1:=by
  have h1:leftE (∅:Finset I)=∅:=by ext; simp[leftE]
  have h2:spent (∅:Finset I)= ∅ := by ext; simp[spent]
  have he:ops (∅:Finset I)=∅:=by ext; simp[ops]
  unfold hue; rw [if_pos]
  · apply Subtype.ext; change light _ (dye g P t _ _)=1; rw [dipping]; simp [made,h1,h2,axle,he]
  simp [Rise.spare,closeS,h2,Rise.wish,brimW]
include h
lemma hue_product (s: Finset (Finset I))(U:Grid f)(ht:P.Wave t)(hp:(s:Set (Finset I)).PairwiseDisjoint (fun p=>p.biUnion M))(hr:(s:Set (Finset I)).PairwiseDisjoint id):
    hue g P t (s.biUnion id) U=∏ p∈s,hue g P t p U:=by
    induction s using Finset.induction_on with
    | empty=> rw [biUnion_empty,hue_origin,prod_empty]
    | insert i s hi ih=>
      have hQ : Disjoint i (s.biUnion id) := Finset.disjoint_left.mpr (fun j hj hk=>by
        obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hk; exact Finset.disjoint_left.mp (hr (mem_insert_self ..) (mem_insert_of_mem hk) (fun he=>hi (he ▸ hk))) hj hz)
      have hP : Disjoint (i.biUnion M) ((s.biUnion id).biUnion M) := Finset.disjoint_left.mpr fun j hj hk=>by
        obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hk; obtain ⟨p,hp',hk⟩:=mem_biUnion.mp hk; exact Finset.disjoint_left.mp (hp (mem_insert_self ..) (mem_insert_of_mem hp') (fun he=> hi (he ▸ hp'))) hj (mem_biUnion.mpr ⟨k,hk,hz⟩)
      rw [biUnion_insert,id_eq,prod_insert hi,hue_join g P t h ht hQ hP]; apply congr_arg
      exact ih (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert ..)) hp) (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert ..)) hr)
end YM.QCD.Cove
