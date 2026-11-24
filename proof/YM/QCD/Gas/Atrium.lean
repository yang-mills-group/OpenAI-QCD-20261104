import YM.QCD.Gas.Pavilion
import YM.Further.SHELL_BIRTH_49.Fusing.Coal
/-! # Optional attachments disjoint except per catalogue. exact bank entries -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.GasP
open Push.AbsoluteSums Partition Relation Graph Ursell Finset Gas Function RG Lattice Wilson Trees
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Classical Topology
variable {ι K κ:Type*}[NormedCommRing K][NormOneClass K][NormedAlgebra ℚ K][NormedAlgebra ℝ K][CompleteSpace K]
variable {n:Side}(p d : ι→ Support n)(q:κ→ Support n) (W: Support n)(u:ι→K)(g:κ→K)
-- same site planet
local notation "X"=> Finset ι
local notation "J"=>ι⊕Support n
local notation "U"=>Finset J
def obscures (r:X): Prop:= separated (blocked p) r ∧ r.biUnion d=W
def pongs (r:X) (x: Finset (Support n)):Prop:= ∀ i∈x,¬Disjoint (r.biUnion p) i
noncomputable def dropsP (i:Support n):K:= NormedSpace.exp (-portion q g i)-1
def wings (v:Finset U): Support n:= (v.biUnion Finset.toLeft).biUnion d
def facesP : J→ Support n:= Sum.elim p id
def wound (v:U):=v.biUnion (facesP p)
def wagon (v:U):Prop:= v.toLeft.Nonempty ∧ Ac.Spark (facesP p) v ∧ separated (blocked p) v.toLeft∧ pongs p v.toLeft v.toRight
def wide (s:Finset U): Prop:= (∀ i∈s,wagon p i) ∧ (s:Set U).PairwiseDisjoint (wound p)
def sweep (r:U):= r.toLeft.biUnion d
-- extra eligibility requires true flag reading. via wings condition
noncomputable def samples : J→K := Sum.elim u (dropsP q g)
noncomputable def motto (r:U):K:=if wagon p r ∧ W∩wound p r=sweep d r then ∏ j∈r,samples q u g j else 0
noncomputable def ward (s:Finset U):K:= if wide p s ∧ wings d s=W then ∏ i∈s,motto p d q W u g i else 0
noncomputable def tableP (r:U):K:=if obscures p d W r.toLeft∧pongs p r.toLeft r.toRight then ∏ j∈r,samples q u g j else 0

lemma flow_in (v:Finset U)(w:Support n):wings d v=w ↔ (v.biUnion id).toLeft.biUnion d=w:=by rw [show (v.biUnion id).toLeft=v.biUnion Finset.toLeft from by ext; simp,wings]

variable {p d} (hp:∀ i,d i⊆ p i)
lemma wing_cost (v:Finset (Finset (ι⊕Support n))) : wings d v=v.biUnion (sweep d):=by ext i; simp [wings,sweep, mem_biUnion]; grind
lemma apart (v:Finset U)(he:wide p v): (v:Set U).PairwiseDisjoint id:= by
    have hx : Ac.Parts (facesP p) (v.biUnion id)=v:= Ac.separates _ _ (fun i hi=> (he.1 i hi).2.1) he.2
    exact hx ▸ Ac.different _ _
include hp
lemma attaining (v:Finset U) (he:wide p v) (hv:wings d v=W) (z:U)(hz:z∈v): W∩wound p z=sweep d z:=by
   rw [← hv,wing_cost v]; have hA s (i) (hi:i∈sweep d s): i∈wound p s:=by obtain ⟨k,hk,hi⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨.inl k,mem_toLeft.mp hk,hp k hi⟩
   ext i; constructor
   · intro h; obtain ⟨hw,hx⟩:=mem_inter.mp h; obtain ⟨j,hj,h⟩:=mem_biUnion.mp hw; have ht:j=z:=by_contra fun hh=> Finset.disjoint_left.mp (he.2 hj hz hh) (hA j i h) hx; exact ht ▸ h
   intro h; exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨_,hz,h⟩,hA z i h⟩
omit hp
lemma portions (v:Finset U) (he:wide p v) {r:U}(h:r=v.biUnion id):
    separated (blocked p) r.toLeft∧pongs p r.toLeft r.toRight:=by
   have hh (z:J) : z∈ r↔∃ i∈v,z∈i:=by rw [h]; simp
   constructor
   · intro i hi j hj hn hg
     obtain ⟨a,ha,hi⟩:=(hh _).1 (mem_toLeft.mp hi); obtain ⟨b,hb,hj⟩:=(hh _).1 (mem_toLeft.mp hj); by_cases ht:a=b
     · subst b; exact (he.1 _ ha).2.2.1 i (mem_toLeft.mpr hi) j (mem_toLeft.mpr hj) hn hg
     rcases hg with hg|⟨u,hU,hV⟩; · exact hn hg
     apply Finset.disjoint_left.mp (he.2 ha hb ht)
     · -- orientation j meets i
       exact mem_biUnion.mpr ⟨.inl i,hi,hU⟩
     exact mem_biUnion.mpr ⟨.inl j,hj,hV⟩
   intro i hi; obtain ⟨a,ha,hi⟩:=(hh _).1 (mem_toRight.mp hi); have hx: a.toLeft⊆r.toLeft:=fun j hj=>mem_toLeft.mpr ((hh _).2 ⟨a,ha,mem_toLeft.mp hj⟩)
   intro hd; apply (he.1 a ha).2.2.2 i (mem_toRight.mpr hi); exact hd.mono_left (fun j h=> by obtain ⟨x,he,hj⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨x,hx he,hj⟩)

lemma seated (u:U)(he: separated (blocked p) u.toLeft)(ht:pongs p u.toLeft u.toRight): wide p (Ac.Parts (facesP p) u):=by
   refine ⟨fun i hi=>?_,Ac.separate _ _⟩ -- sig
   obtain ⟨hI,h⟩:= Ac.lives (facesP p) _ hi -- lemma
   have hv:i.toLeft⊆u.toLeft:=fun j hj=>mem_toLeft.mpr (hI (mem_toLeft.mp hj))
   have hx: pongs p i.toLeft i.toRight:=by
     intro j hj; obtain ⟨x,hx,hK⟩:=not_disjoint_iff.mp (ht j (mem_toRight.mpr (hI (mem_toRight.mp hj)))); refine not_disjoint_iff.mpr ⟨x,?_,hK⟩
     obtain ⟨a,ha,hx⟩:=mem_biUnion.mp hx
     have hR:.inl a ∈ i:= by
       have hg : .inl a∈u:=mem_toLeft.mp ha
       by_contra hn
       rw [← Ac.reconstruct (facesP p) u] at hg;
       obtain ⟨b,hb,hb'⟩:=mem_biUnion.mp hg
       exact Finset.disjoint_left.mp ((Ac.separate (facesP p) u) hb hi (fun h=> hn (h ▸ hb'))) (mem_biUnion.mpr ⟨.inl a,hb',hx⟩) (mem_biUnion.mpr ⟨.inr j, mem_toRight.mp hj,hK⟩)
     exact mem_biUnion.mpr ⟨a,mem_toLeft.mpr hR,hx⟩
   refine ⟨?_,h,(fun j hj k hk=>he j (hv hj) k (hv hk)),hx⟩
   obtain ⟨a,ha⟩:=h.1
   cases a with
   | inl a=> exact ⟨_,mem_toLeft.mpr ha⟩
   | inr a=> obtain ⟨x,hx,hy⟩:= not_disjoint_iff.mp (hx a (mem_toRight.mpr ha)); obtain ⟨y,hy,hk⟩:= mem_biUnion.mp hx; exact ⟨y,hy⟩
include hp
lemma resumes (v: Finset U)(he: wide p v) : tableP p d q W u g (v.biUnion id)=ward p d q W u g v:=by
   obtain ⟨hv,hx⟩:= portions v he rfl; unfold tableP ward; by_cases hx':wings d v=W
   · rw [if_pos ⟨⟨hv,(flow_in d v W).1 hx'⟩,hx⟩,if_pos ⟨he,hx'⟩,Finset.prod_biUnion (apart _ he)]
     exact prod_congr rfl fun x hx=> (if_pos ⟨he.1 _ hx, attaining W hp v he hx' x hx⟩).symm
   rw [if_neg (fun h=>hx' ((flow_in _ _ _).2 h.1.2)),if_neg (fun h=>hx' h.2)]
end YM.QCD.GasP
