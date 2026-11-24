import YM.Intag.Column
import YM.Lyre.Absolute
import YM.Lyre.Price
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical
namespace Pilgrim
variable {l c f:Side}(T:Tiling f)(p:T.Cell)
-- breadth # ≤8 for ONE system. Choose coherent array over all cells.
noncomputable def dT (u:T.Cell):ℕ:= Nat.find (show ∃ k,∃ l:TapeWalk f T,l.length=k∧ finish T p l=u from by obtain ⟨l,h⟩:= connect p u; exact ⟨l.length,l,rfl,h⟩) -- wrong .imp
lemma self : dT T p p=0:=Nat.eq_zero_of_le_zero (Nat.find_min' _ ⟨[],rfl,rfl⟩)
lemma routes (u:T.Cell): dT T p u≤8:=by obtain ⟨l,h,hp⟩:= legsT T p u; exact (Nat.find_min' _ ⟨l,rfl,hp⟩).trans h
lemma jets (u:T.Cell)(hu:u≠p): ∃ (v:T.Cell×T.Cell×Axis), dT T p v.1 < dT T p u∧u=T.mate v.2.1 v.2.2 v.1:=by
      obtain ⟨l,h,hx⟩:= (show ∃ l:TapeWalk f T,l.length=dT T p u∧finish T p l=u from (by unfold dT; exact Nat.find_spec (p:=fun n=>∃ l:TapeWalk f T,l.length=n∧finish T p l=u) (by obtain ⟨l,h⟩:=connect p u; exact ⟨_,l,rfl,h⟩)))
      cases l with
      | nil=>exact False.elim (hu hx.symm)
      | cons a l=> let v:=finish T p l; have hh:finish T p (a::l)=T.mate a.1 a.2 v:=rfl
                   exact ⟨(v,a), lt_of_le_of_lt (Nat.find_min' _ ⟨l,rfl,(rfl: finish T p l=v)⟩) (h ▸ by simp),hx.symm.trans hh⟩
-- chosen tree parent
noncomputable def before (u:T.Cell):T.Cell × T.Cell×Axis:= if h:u=p then (p,p,(0:Axis)) else Classical.choose (jets T p u h)
noncomputable abbrev μ (u:T.Cell) := (before T p u).1
noncomputable abbrev post (u:T.Cell):= (before T p u).2
lemma forester {u:T.Cell}(hu:u≠p): dT T p (μ T p u) < dT T p u∧u=T.mate (post T p u).1 (post T p u).2 (μ T p u):=by
       unfold μ post before; rw [dif_neg hu]; exact Classical.choose_spec (jets T p u hu)
noncomputable def crestT (u:T.Cell): TapeWalk f T := if h:u=p then [] else post T p u::crestT (μ T p u)
termination_by dT T p u
decreasing_by exact (forester _ _ h).1
lemma path (u:T.Cell) : finish T p (crestT T p u)=u∧(crestT T p u).length ≤dT T p u:=by
    rw [crestT]; split_ifs with h
    · subst u; exact ⟨rfl,Nat.zero_le _⟩
    have hQ:=path (μ T p u); obtain ⟨h1,h2⟩:= forester T p h; let V:=μ T p u; change T.mate _ _ (finish T p (crestT T p V)) =_ ∧ _; rw [show finish T p (crestT T p V)=V from hQ.1,List.length_cons]; exact ⟨h2.symm,Nat.succ_le_of_lt (lt_of_le_of_lt hQ.2 h1)⟩
termination_by dT T p u
decreasing_by exact (forester _ _ h).1
lemma at_p : crestT T p p=[] := by rw [crestT,dif_pos rfl] -- rfl tactic ambiguity
lemma away_p {u:T.Cell}(hu:u≠p) : crestT T p u= post T p u::crestT T p (μ T p u) := by rw [crestT,dif_neg hu]
variable (h:T.kind=.link)
include h
omit h
noncomputable def passport (h:T.kind=.link){u:T.Cell}: Cover:= Classical.choose (shone (T.bandCut (post T p u).1 (post T p u).2) (show _=_ from h)) -- implicit not included? macro.Free var.
set_option quotPrecheck false
local notation "C" u:arg=> T.bandCut (post T p u).1 (post T p u).2
include h
lemma paced (u:T.Cell) : CompleteP (C u) (passport T p h (u:=u)):= by unfold passport; exact Classical.choose_spec _
noncomputable def flip (u:T.Cell): Signed:= Signed.mirror (post T p u).2
-- unconditional shifts real covariant AP. and replica lifts from ℓ pitch to all positions.
omit h
noncomputable def bout (h:T.kind=.link)(x:Cover)(u:T.Cell): Cover := if he:u=p then x else (C u).flip.act (bout h x (μ T p u))+ passport T p h (u:=u)
termination_by dT T p u
decreasing_by exact (forester T p he).1
variable (x₁:Cover)
include h
lemma quail (w:Site f)(hp:T.copyMap p w=wrap f x₁)(u:T.Cell): wrap f (bout T p h x₁ u) = T.copyMap u w:=by
        rw [bout]; split_ifs with hV; · subst u; exact hp.symm
        have he:= quail w hp (μ T p u)
        rw [map_add,← wrap_signed,he,(paced T p h u).aligned]; exact Eq.symm ((congr_arg (fun v=>T.copyMap v w) (forester T p hV).2).trans (T.after _ _ _ w))
termination_by dT T p u
decreasing_by exact (forester T p hV).1
omit h
-- King itinerary law through projection.H. for any lifted tiling.B.Datac. only needs hM equality. For Chess.Serve.
variable (g:Ratio c f)(x:Site f)(G:Ratio c l)(r:Ratio f l)(X:Site l)(ho:Even c.val)(P:Site c)
local notation "S!"=>mural g ho x
local notation "T!"=>mural G ho X
lemma liftL (L:TapeWalk f (mural g ho x)): finish (T!) P L= finish (S!) P L:=by induction L with| nil=>rfl| cons i l ih=> change (T!).mate i.1 i.2 _=(S!).mate i.1 i.2 _; rw [ih]; rfl -- T.Cell cast
open QCD.Lat Massive.Chess
variable (Y:Site c→ Stud l 6)
set_option quotPrecheck false
local notation "W" p:arg=> post S! P p
lemma income (he: ∀ j:Site c,j ≠ P → let u:= W j; Y j=tallH ((T!).bandCut u.1 u.2) (Y (μ S! P j))) (hP: Lyre.Potion (Y P))(u:Site c): SignedEq (palmH (T!) (Y P) P u) (Y u):=by
        suffices hp:∀ v:Site c,Y v= road (pathT (T!) (crestT (S!) P v)) (Y P) by rw[hp u]; exact (bookR _ (T!) _ _ _ hP rfl ((liftL g x G X ho P _).trans (path _ _ u|>.1))).symm -- rw risk Y p if u syntactic
        intro v
        generalize ht : dT (S!) P v=n; induction n using Nat.strong_induction_on generalizing v with
        | h n ih => rcases eq_or_ne v P with ht'|ht'
                    · subst v; rw [at_p S! P]; rfl
                    let u:=μ (S!) P v; have hk:dT S! P u<n:= ht ▸ (forester S! P ht').1
                    rw [away_p S! P ht']; let A:=(S!); change _ = road ((mural G ho X|>.bandCut (post A P v).1 (post A P v).2)::pathT (T!) (crestT S! P u)) (Y P); rw [road]; exact (he v ht').trans (congr_arg _ (ih _ hk u rfl))
end Pilgrim
end YM.Intag
#print axioms YM.Intag.Pilgrim.quail
#print axioms YM.Intag.Pilgrim.routes
#print axioms YM.Intag.Pilgrim.income
