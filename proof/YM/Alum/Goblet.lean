import YM.Intag.Shift
import YM.Intag.Dwells
import YM.Lyre.Bloom
/-!
# Subdivision replica prices.
Use actual cut itineraries of the smaller stencil price. Signs not discarded
inside operator polynomials. Purely bound after correlation with nuclei.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass Set
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet
variable {n c l d:Side}{F:ℕ}
open Chess Cells Romance Massive.Lyre.Array Plum
-- general sign congruences, path cost carried on actual ops.
lemma signedWords {A:Type*}[Neg A] (x:A): SignedEq x x:= SignedEq.refl _
lemma applauds (T:Tiling n)(l:TapeWalk n T)(x y:Stud n F)(h:SignedEq x y): SignedEq (road (pathT T l) x) (road (pathT T l) y):=by
    rcases h with h|h; exact Or.inl (h ▸ rfl); exact Or.inr (by rw[h,road_neg])
lemma signsList {J:Type*}(L:List J)(x y:J→Stud n F)(h:∀ i,SignedEq (x i) (y i)): SignedEq (L.map x).prod (L.map y).prod:=by
    induction L with|nil=>exact SignedEq.refl _| cons a l ih=> exact signsM (h a) ih
lemma potMul {x y:Stud n F}(hx:Potion x)(hy:Potion y):Potion (x*y):=by obtain ⟨p,h⟩:=hx; obtain ⟨q,H⟩:=hy; exact ⟨_,fun U=>(h U).mul (H U)⟩
lemma potProd {J:Type*}(L:List J)(x:J→Stud n F)(h:∀ i∈L,Potion (x i)): Potion (L.map x).prod:=by
    induction L with| nil=> exact ⟨false,fun U=> by change Hom false 1; simp [Hom,Plus]⟩| cons a l ih=> exact potMul (h a (by simp)) (ih fun i hi=>h _ (by simp[hi]))
lemma potW (L:List (Band n))(x:Stud n F)(hx:Potion x):Potion (road L x):=by obtain ⟨p,h⟩:=hx; exact ⟨_,road_parity L x p h⟩
lemma signed_rearr {J:Type*}(L M : List J)(h:L.Perm M)(x:J→Stud n F)(hp:∀ i,Potion (x i)): SignedEq (L.map x).prod (M.map x).prod:=by
    induction h with| nil=>exact SignedEq.refl _|cons a _ ih=>exact signsM (SignedEq.refl _) ih|swap a b l=> simp only [List.map_cons,List.prod_cons,← mul_assoc]; exact signsM ((hp a).swap _ _ (hp b)) (SignedEq.refl _) | trans _ _ i j=> exact SignedEq.trans i j
lemma potscaling {x:Stud n F}(h:Potion x)(z:ℂ): Potion (z • x):=by obtain ⟨p,h⟩:=h; exact ⟨p,fun U=>(h U).smul _⟩
lemma productView {J:Type*}(L:List J)(x:J→Stud n F)(P:Cells.Cut n): tallH P ((L.map x).prod)=(L.reverse.map (fun i=>tallH P (x i))).prod:=by
    induction L with|nil=>exact smogOne|cons a L ih=>simpa only [List.map_cons,List.prod_cons,List.reverse_cons,List.map_append,List.prod_append,List.map_nil,List.prod_nil,mul_one] using ((coatM (C:=P) (x a) (L.map x).prod).trans (by rw [ih] :tallH P (L.map x).prod*tallH P (x a)=(L.reverse.map _).prod*tallH P (x a))) -- ambiguous
lemma royalties {J:Type*}(L:List J)(x:J→Stud n F)(T:Tiling n)(l:TapeWalk n T)(h:∀ i,Potion (x i)): SignedEq (road (pathT T l) (L.map x).prod) ((L.map fun i=>road (pathT T l) (x i)).prod):=by
    induction l with
    | nil=> exact SignedEq.refl _
    | cons u l ih=> let b:= T.bandCut u.1 u.2; let y(i:J):= tallH b (road (pathT T l) (x i))
                    apply (applauds T [u] _ _ ih).trans -- rfl
                    change SignedEq (tallH b (L.map (fun i=>road (pathT T l) (x i))).prod) (L.map y).prod; rw [productView]; exact signed_rearr L.reverse L (List.reverse_perm L) y fun i=>potW (pathT T (u::l)) (x i) (h i)
-- top_fee invariant under admissible path.
lemma earn_eq(T:Tiling n)(hp:T.kind=.link)(R:Regulator n F)(p:T.Cell)(x:Stud n F)(hx:Potion x)(l:TapeWalk n T)(q:T.Cell)(hz:finish T p l=q)(y:Stud n F)(hy:Potion y)(he:SignedEq (road (pathT T l) x) y) : topH T R x p=topH T R y q:=by
     have hh (v:T.Cell):SignedEq (palmH T x p v) (palmH T y q v):=by
          let L:= tag T q v; let w:= L++l; apply ((Lyre.bookR x T p v w hx hp (?_)).symm).trans
          rw [show pathT T w=pathT T L++pathT T l from List.map_append,road_app]; exact applauds _ L _ _ he
          rw [show w=_ from rfl, app, hz, show finish T q L=v from tag_spec ..]
     exact (pow_left_inj₀ (top_nn ..) (top_nn ..) T.cells_positive.ne').1 (by rw [top_power,top_power]; exact signsV R (signsList _ _ _ hh))
-- when a layer-complement fits.
variable (T W : Tiling n)
structure Ladder where
    g : T.Cell × Axis→ W.Cell × Axis
    c a : W.bandCut (g a).1 (g a).2 = T.bandCut a.1 a.2
namespace Ladder
variable {T W}(E:Ladder T W)
lemma taps (l:TapeWalk n T): pathT W (l.map E.g)=pathT T l:= by
   induction l with|nil=>rfl| cons a l ih=> exact congr_arg₂ List.cons (E.c a) ih
lemma nested (l:TapeWalk n T)(p:T.Cell)(q:W.Cell)(he: W.chamber q ⊆ T.chamber p): W.chamber (finish W q (l.map E.g)) ⊆ T.chamber (finish T p l):=by
   induction l with
   | nil=> exact he
   | cons a l ih=>
        intro x hx; let b:=T.bandCut a.1 a.2; let y:=b.reflect x; have hy:y∈W.chamber (finish W q (l.map E.g)):=by
            have hW:= Massive.Romance.chamber W (E.g a).1 _ (E.g a).2 hx; change x∈W.chamber (W.mate (E.g a).1 (E.g a).2 _) at hx; -- defeq rw
            change (W.bandCut (E.g a).1 (E.g a).2).reflect x∈ W.chamber (W.mate (E.g a).1 (E.g a).2 (finish W q ((a :: l).map E.g))) at hW
            rw [List.map_cons,finish,W.mate_invol,E.c] at hW; exact hW
        have hV:= Massive.Romance.chamber T a.1 (finish T p l) a.2 (ih hy); change b.reflect y ∈ _ at hV; unfold y at hV; rw [b.twice] at hV; exact hV
lemma going (l:TapeWalk n T):Injective (fun q:W.Cell=>finish W q (l.map E.g)):=by
     induction l with
     | nil=> exact injective_id
     | cons a l ih=> exact ((show Involutive _ from Tiling.mate_invol W (E.g a).1 (E.g a).2)|>.injective).comp ih -- field notation error
lemma disjointJ (l:T.Cell→TapeWalk n T)(u:T.Cell)(he:∀ i,finish T u (l i)=i){I:Type*}(P:I→W.Cell)(hx:∀ i,W.chamber (P i)⊆T.chamber u)(hn:∀ j,(W.chamber j).Nonempty)(hr:Injective P):Injective (fun i : T.Cell× I=>finish W (P i.2) ((l i.1).map E.g)):=by
    intro i j hv; change finish W (P i.2) ((l i.1).map _) = finish W (P j.2) ((l j.1).map _) at hv; obtain ⟨x,h⟩:=hn (finish W (P i.2) ((l i.1).map E.g)); have hk:x∈T.chamber i.1:= (he i.1) ▸ E.nested _ u _ (hx i.2) h; have hu:x∈T.chamber j.1:= (he j.1) ▸ E.nested _ u _ (hx j.2) (hv ▸ h); have hp:i.1=j.1:= (T.which_chamber hk).symm.trans (T.which_chamber hu); change finish W (P i.2) ((l i.1).map _) = finish W _ _ at hv; rw [hp] at hv; exact Prod.ext hp (hr (E.going _ hv))
end Ladder
end Goblet
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.Ladder.disjointJ
#print axioms YM.Massive.Lyre.Goblet.royalties
#print axioms YM.Massive.Lyre.Goblet.earn_eq
