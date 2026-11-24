import YM.Pods.Coins
import YM.Cells.Packing
/-! Link centers from arbitrary Runs. Always mosaic, short wave orientation path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix
namespace Romance
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
variable {n c : Side} (g:Ratio c n) (T:Cells.Tiling n)
-- centered o anywhere. centerRoot lifted. local replica.X ≤8 axis count. not used for geometry.Adj.Mixed.
variable (he:Even c.val) (hp: Odd g.count.val)
include he
noncomputable def mural (x:Site n) : Cells.Tiling n where
    period:=c
    units:=g
    widthHalf:= ⟨c.val/2, by change Nat.succ 0 ≤ c.val/2; have ht:c.val≥1:=c.property; obtain ⟨k,hk⟩:=he; apply Nat.div_pos (show 2 ≤ _ from ?_) (by norm_num); omega⟩
    even:=by change c.val=2*(c.val/2); obtain ⟨k,h⟩:=he; omega
    kind:= .link
    base:=fun i=> x i-(((g.count.val/2:ℕ)): Per n)
omit he
-- center copy.Cases from old.
include he hp
local notation "L"=>g.count.val
local notation "T₀"=> mural g he
variable (x:Site n)(v:Site c)
lemma tuned : (T₀ x).copyMap v x=x+g.embed v:=by
    funext i; let f:= T₀ x; let P:= (L/2); let p:Per n:= P
    have hL : L=P+P+1:=by obtain ⟨j,hj⟩:= hp; omega
    have hx : x i-f.base i=p:= sub_sub_cancel ..
    have hu:= (f.copy_formula v x i); rw [hx] at hu
    have ht : (L: Per n)=p+p+1:=by unfold p; rw [hL,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    let G:= f.copyMap v x i; have hh : G-(f.starts v i)=p:=by
        split at hu
        · exact hu.trans (show (L:Per n)-↑Kind.link.shift-p=p from by rw [ht, Kind.shift]; push_cast; abel)
        exact hu
    change G=x i + _; calc
      _ = p+f.starts v i:=sub_eq_iff_eq_add.mp hh
      _ = p+((f.base i)+ (g.embed v i)):=rfl
      _ = _:= by rw [← hx]; abel
lemma lies : x ∈ (T₀ x).chamber 0:=by
    intro i; let f:= T₀ x; change (x i-f.starts 0 i).val < _; rw [f.starts_zero]; change (x i-(x i-_)).val<L; rw [sub_sub_cancel]
    have hx:L≤ n.val:= g.exact_size ▸ le_mul_of_one_le_left (Nat.zero_le _) c.property; rw [ZMod.val_natCast_of_lt (show L/2<n.val from (Nat.div_lt_self g.count.pos (by omega)).trans_le hx)]; exact Nat.div_lt_self g.count.pos (by omega)
omit he hp
-- choose other path short.Len depends only rank. use mod explicit solve.
lemma axisReach (p q:T.Cell)(a:Axis): ∃ l:TapeWalk n T, l.length≤2∧ finish T p l=update p a (q a):=by
    let x:=q a-p a; obtain ⟨j,h⟩|⟨j,h⟩:=Nat.even_or_odd x.val
    · let u:= T.mate p a p; let z:= update p a (p a+(j: Per T.period)); refine ⟨[(z,a),(p,a)],by simp,?_⟩
      have he: q a=p a+(j:Per T.period)+j:=by
          have he: (x.val:Per T.period)=q a-p a:= ZMod.natCast_zmod_val x; rw [h,Nat.cast_add] at he; rw [add_assoc,he]; abel
      ext i; by_cases ht:i=a; · subst i; simp only [Romance.finish,Cells.Tiling.mate_here, z,update_self]; rw [he]; ring
      rw [finish,T.mate_off z a _ ht,finish,finish,T.mate_off p a p ht]; exact (update_of_ne ht ..).symm
    · let z:=update p a (p a+j+1); refine ⟨[(z,a)],by simp,?_⟩
      have he: q a=p a+(j:Per T.period)+j+1:=by
          have he:(x.val:Per T.period)=q a-p a:= ZMod.natCast_zmod_val x; rw [h] at he; push_cast at he; rw [two_mul] at he; rw [show p a+(j:Per T.period)+j+1=p a+(j+j+1) by ring,he]; abel -- scopes Nat cast.T
      ext i; by_cases ht:i=a; · subst i; simp [finish,z,he]; ring
      change T.mate z a p i= _; rw [T.mate_off z a _ ht]; exact (update_of_ne ht ..).symm
lemma legsT (P Q:T.Cell): ∃ l:TapeWalk n T,l.length≤8 ∧ finish T P l=Q:=by
     have h (p:Finset Axis): ∃ l:TapeWalk n T, l.length ≤2*p.card∧ ∀ i∈p, finish T P l i=Q i:=by
        induction p using Finset.induction_on with
        | empty=>exact ⟨[],by simp,by simp⟩
        | insert i s hi ih=>
            obtain ⟨l,he,h⟩:=ih; obtain ⟨k,hv,hk⟩:= axisReach T (finish T P l) Q i; refine ⟨k++l, by rw [card_insert_of_notMem hi,List.length_append]; omega,?_⟩; rw [app,hk]; intro j hj; rcases mem_insert.mp hj with hj|hj; · subst i; simp
            rw [Function.update_of_ne (show j≠ i from fun ht=>hi (ht ▸ hj)),h j hj]
     obtain ⟨p,H,h⟩:= h Finset.univ; exact ⟨_,by simpa using H,funext fun i=>h i (mem_univ _)⟩
end Romance
end YM.Massive
#print axioms YM.Massive.Romance.tuned
#print axioms YM.Massive.Romance.lies
#print axioms YM.Massive.Romance.legsT
