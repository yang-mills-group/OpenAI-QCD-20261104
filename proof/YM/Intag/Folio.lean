import YM.Lyre.Packs
import YM.Intag.Column
import YM.Intag.Films
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open MassiveQCD.Cupola MassiveQCD.Cape MassiveQCD.Cape.LampV MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden
open scoped BigOperators Classical Matrix.Norms.L2Operator
namespace Folio
open Finset
variable {I:Type}[Fintype I]{p q l:Side}(U : I → Site p)(R:Site p→List I)
-- allocation and bill.L f maps to actual letters. TypeB one-per P. TypeA arbitrary breadth up to appoint before L. Opaque Enum override.DecideEq. Includes partition.Power.V. orientation proof independent.
noncomputable def ink (U:I→Site p):Finset (Finset I):= Finset.univ.filter fun k=> (k.image U).card ≤ 1
lemma ort (k:Finset I) : k∈ink U ↔ ∀ i∈ k,∀ j∈k,U i=U j:=by
     unfold ink; rw [Finset.mem_filter,and_iff_right (mem_univ _),card_le_one]; constructor
     · intro h i hi j hj; exact h _ (mem_image_of_mem U hi) _ (mem_image_of_mem U hj)
     intro h i hi j hj; obtain ⟨x,hx,rfl⟩:=mem_image.mp hi; obtain ⟨y,hy,rfl⟩:=mem_image.mp hj; exact h x hx y hy
variable (k M b B:ℕ)(hc:Fires U k)
lemma area (K t:Finset I)(h:t⊆K)(hv:K∈ink U): t∈ink U:= (ort U t).mpr fun i hi j hj=> (ort ..).1 hv i (h hi) j (h hj)
@[simp] lemma singleInk (i): {i}∈ink U:= by unfold ink; simp
@[simp] lemma dustInk : ∅ ∈ ink U:= by unfold ink; simp
include hc
lemma volume (K:Finset I)(h:K∈ink U): K.card ≤k :=by
     obtain hh|⟨i,hi⟩:= K.eq_empty_or_nonempty; simp [hh]
     exact (Finset.card_le_card (show K ⊆ _ from fun x hx=> mem_filter.mpr ⟨mem_univ _,(ort ..).1 h _ hx _ hi⟩)).trans (hc (U i)) -- fix metas
lemma leaves (j:I): ((ink U).filter (fun i=>j∈i)).card ≤2^k:=by
     let B:=univ.filter (fun i:I=> U i=U j); have hv:(ink U).filter (fun i=>j∈i)⊆ B.powerset :=by
          intro X hx; obtain ⟨h₁,h₂⟩:= mem_filter.mp hx; exact mem_powerset.mpr (fun x h=> mem_filter.mpr ⟨mem_univ _,(ort ..).mp h₁ _ h _ h₂⟩)
     exact (Finset.card_le_card hv).trans ((card_powerset B).le.trans (Nat.pow_le_pow_right (by norm_num) (hc (U j))))
omit hc
-- posterior enumeration.Vectors.Transport. authorize correction.Public.Word.
structure Muster (U:I→Site p)(R:Site p→List I): Prop where
      order (i) : (R i).Nodup
      address (i x) : x∈R i ↔ U x=i
variable (h:Muster U R)

private lemma preSpec {A J:Type}(l:List J)(V:J→List A)(k:Finset A): k∈ allV l V ↔ ∃ i∈l, k.Nonempty ∧ ∀ x∈ k,x ∈ V i:=by -- check Fintype A
   unfold allV; rw [mem_biUnion]; simp only [comp_apply,bindV,mem_erase, mem_powerset, List.mem_toFinset,Finset.nonempty_iff_ne_empty,Finset.subset_iff]
include h
lemma named (d: List (Site p))(hv:d.Nodup) : (d.flatMap R).Nodup:=by
      induction d with
      | nil=>simp
      | cons i l ih=> rw[List.flatMap_cons]; have hp := List.nodup_cons.mp hv
                      refine List.nodup_append.mpr ⟨h.order i,ih hp.2,?_⟩
                      intro x hx y hy he; subst y; obtain ⟨j,hj,hv⟩:= List.mem_flatMap.mp hy; exact hp.1 ( (((h.address i x).1 hx).symm.trans ((h.address j x).1 hv)).symm ▸ hj)
lemma landed : (((univ:Finset (Site p)).toList).flatMap R).Nodup ∧ (((univ:Finset (Site p)).toList).flatMap R).toFinset = univ:=by
    exact ⟨named U _ h _ (nodup_toList _), eq_univ_iff_forall.mpr fun i=> List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨U i,mem_toList.mpr (mem_univ _),(h.address _ _).mpr rfl⟩)⟩
lemma prepay : (ink U).erase (∅:Finset I)= allV (univ:Finset (Site p)).toList R:=by -- actual instances for ink.fi.ensure
    ext1 K; rw [preSpec]; constructor
    · intro hx; obtain ⟨ht,hv⟩:= mem_erase.mp hx; obtain ⟨x,hx'⟩:= Finset.nonempty_iff_ne_empty.mpr ht
      exact ⟨U x,mem_toList.mpr (Finset.mem_univ _), ⟨x,hx'⟩, fun y hy =>(h.address _ _).mpr ((ort ..).1 hv y hy x hx') ⟩
    rintro ⟨i,_,he,hp⟩; exact mem_erase.mpr ⟨he.ne_empty,(ort ..).mpr fun x hh y hv=> ((h.address _ x).mp (hp x hh)).trans ((h.address _ y).mp (hp y hv)).symm⟩

omit h
variable (pᵢ:I→Site l)(g:Ratio p l)(s:Ratio q l)(z:Site l)(he:Even p.val)(ho:Odd g.count.val)(hr: Odd s.count.val)
variable (hGX:∀ i,pᵢ i∈ (mural g he z).margin (U i) M)
-- Geometry hypotheses.Core type any. value inputs.S.Spark.A.Anchor and Flag budgets.
include hr hGX ho hc
lemma films (hx:s.count.val*(B*B+1) ≤2*M): ClusteredE U (ink U) k B (s.parent∘pᵢ):=Film.garden _ _ hr _ U he ho _ hGX _ (volume _ _ hc) hc (fun t _ hlo=> mem_filter.mpr ⟨mem_univ _,hlo⟩) hx
omit hGX ho hc
open MassiveQCD.Play
lemma lit (hv:∀ i j,U i=U j→ separation (pᵢ i) (pᵢ j) ≤ s.count.val)(ht:0<B): ∀ k∈ink U, k.Nonempty→ Ac.Spark (Camp.Ray (s.parent∘pᵢ) (baseTZ B)) k:=Film.sparks s hr pᵢ (ink U) (baseTZ B) (fun k hk i hi j hj=> hv i j ((ort ..).mp hk i hi j hj)) (by unfold baseTZ; omega)
end Folio
end YM.Intag
#print axioms YM.Intag.Folio.volume
#print axioms YM.Intag.Folio.leaves
#print axioms YM.Intag.Folio.lit
#print axioms YM.Intag.Folio.films
#print axioms YM.Intag.Folio.prepay
#print axioms YM.Intag.Folio.landed
