import YM.QCD.Cove.Lid
import YM.Further.SHELL_BIRTH_49.Fusing.Coal
/-! # disjoint molecule decomposition for alloy. No overestimate of Grassmann valence.
Mask core padded by trim+1 permits Camp test regardless of exterior flags.
-/
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
variable (g:Send S F D) (P:Rise f F E J)

-- sector stamp includes all short-field viability margin. all Reads choose wrapper larger than Touch. use radius for gauges later.

def brim (i:Fj D E J):Support f:= halo (g.trim+1) (native g P i)
def brimW (s: Finset (Fj D E J)) := s.biUnion (brim g P)
lemma brim_eq (s: Finset (Fj D E J)):brimW g P s=halo (g.trim+1) (coreW g P s):=by
  ext i; constructor
  · intro h; obtain ⟨u,hu,h⟩:=mem_biUnion.mp h
    exact Corona.halo_mono (le_refl _) (fun i hi=> mem_biUnion.mpr ⟨_,hu,hi⟩) h
  intro h; obtain ⟨m,hm,hh⟩:=halo_spec.mp h; obtain ⟨i,hi,hq⟩:=mem_biUnion.mp hm; exact mem_biUnion.mpr ⟨_,hi,halo_spec.mpr ⟨_,hq,hh⟩⟩
lemma native_sub (s:Finset (Fj D E J)): coreW g P s⊆ brimW g P s:= by rw [brim_eq]; exact halo_subset ..
lemma wish_sub (s : Finset (Fj D E J)): P.wish (spent s)⊆ coreW g P s:= by
  intro i hi; obtain ⟨j,hj,he⟩:= mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨Sum.inr (Sum.inr j),by simpa [spent] using hj,(P.front j).part he⟩

structure Count (M: I→ Support c) :Prop where
 budget i : (brim g P i).image S.parent ⊆ M i
variable {M:Fj D E J → Support c} (h:Count g P M)
include h
lemma totalW (s: Finset I): (brimW g P s).image S.parent ⊆ s.biUnion M:=by
  rintro i hi; obtain ⟨u,hu,rfl⟩:= mem_image.mp hi; obtain ⟨v,hv,hp⟩:=mem_biUnion.mp hu; exact mem_biUnion.mpr ⟨_,hv,h.budget v (mem_image_of_mem _ hp)⟩
lemma remote {s w:Finset I} (hp:Disjoint (s.biUnion M) (w.biUnion M)):Disjoint (brimW g P s) (brimW g P w):=by
  apply Finset.disjoint_left.mpr; intro i hi hv; exact Finset.disjoint_left.mp hp ((totalW g P h s) (mem_image_of_mem _ hi)) ((totalW g P h w) (mem_image_of_mem _ hv))
lemma rotor {s w : Finset I} (hp:Disjoint (s.biUnion M) (w.biUnion M)):Disjoint (hooks (F:=F) S (coreW g P s)) (hooks S (coreW g P w)):= by
  apply Finset.disjoint_left.mpr; intro i hi hv; exact Finset.disjoint_left.mp (remote g P h hp) ((native_sub g P s) ((mem_filter.mp hi).2)) ((native_sub g P w) ((mem_filter.mp hv).2))

omit h
lemma join_ax (U:Grid f){s w:Finset I}(hp: Disjoint s w): axle g U (s∪w)=axle g U s * axle g U w:=by
  have hh: Disjoint (ops s) (ops w):=by
    apply disjoint_left.mpr; intro i hi hv; exact Finset.disjoint_left.mp hp (show Sum.inl i∈s by simpa [ops] using hi) (show Sum.inl i∈w by simpa [ops] using hv)
  unfold axle; rw [noncommProd_congr (show ops (s∪w)=ops s ∪ ops w by ext; simp [ops]) (fun i _=> rfl)]; exact noncommProd_union_of_disjoint hh _ _

lemma make_join (t:ℝ)(U:Grid f){s w:Finset I}(hd:Disjoint s w): made P t U (s∪w)=made P t U s*made P t U w:=by
  have ht: leftE (s∪w)=leftE s∪leftE w:=by ext; simp [leftE]
  have hz: spent (s∪w)=spent s∪spent w:=by ext; simp [spent]
  have hp: Disjoint (leftE s) (leftE w):=by
    refine Finset.disjoint_left.mpr fun i hi hv=> Finset.disjoint_left.mp hd (show Sum.inr (Sum.inl i) ∈ s by simpa [leftE] using hi) (show Sum.inr (Sum.inl i)∈ w by simpa [leftE] using hv)
  have hv: Disjoint (spent s) (spent w):=by
    refine Finset.disjoint_left.mpr fun i hi hv=> Finset.disjoint_left.mp hd (show Sum.inr (Sum.inr i)∈s by simpa [spent] using hi) (show Sum.inr (Sum.inr i)∈ w by simpa [spent] using hv)
  unfold made; rw [ht,hz,prod_union hp,prod_union hv]; ring
include h
lemma dye_join (U:Grid f)(t:ℝ)(ht:P.Wave t){s w : Finset I}(hd:Disjoint s w)(hg:Disjoint (s.biUnion M) (w.biUnion M)):
    dye g P t (s∪w) U=dye g P t s U *dye g P t w U:=by
  unfold dye; rw [← map_mul]; congr 1; apply Subtype.ext
  change axle g U _ (near A B (light _ (made P t U _))) = light _ (crate g P t s U*crate g P t w U); rw [make_join P t U hd,map_mul (light (Keys f F)),map_mul (near A B),map_mul (light R),join_ax g U hd]
  have hm (s:Finset I): near A B (light _ (made P t U s))∈ region (hooks S (coreW g P s)):=by
    apply effects _ _ _ (wears g P t s U ht); intro i hi; change embed (ha c f F) _∈_; rw [embed_atom]; apply marked; rw [hooked,rootA]; exact (mem_filter.mp hi).2
  exact (forces g P U s).paysR (forces g P U w) (rotor g P h hg) (hm s) (hm w) (bright (ahead S F (made P t U s))) (bright (ahead S F (made P t U w)))
end YM.QCD.Cove
