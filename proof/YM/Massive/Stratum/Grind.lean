import YM.Massive.Stratum.Fold
/-!
# Plateau schedules

Widths and prices depend on the finite transition, not consumer index
or actual volume or top/bare depth. A schedule before those choices,
accommodating arbitrary fees chosen after the stride. Run the relation
**backwards** through the schedule, fine→coarse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Stratum
open Relation Filter Set
open scoped Topology

variable {X:Type*}
structure Pavement (H:ℕ→X→X→Prop)(need:ℕ→X→X→ℕ) where
  height : ℕ→ℕ
  sites : ℕ→X
  grows k : height k ≤ height (k+1)
  stays k : height (k+1) ≤ height k+1
  origin : height 0=0
  free : Tendsto height atTop atTop
  links k : H (height k) (sites (k+1)) (sites k)
  enough k : need (height k) (sites (k+1)) (sites k) ≤ k+ need 0 (sites 1) (sites 0)
-- demand for first step guaranteed by at least one steady iteration.
variable {R:X→X→Prop}
private lemma view {x y}(h: ReflTransGen R x y):∃ (n:ℕ)(s:ℕ→X), s 0=y ∧ s n=x ∧ ∀ i<n,R (s (i+1)) (s i):=by
    induction h with
    | refl=> exact ⟨0,fun _=> x,rfl,rfl,fun i h=> by omega⟩
    | @tail z w _ hh ih =>
       obtain ⟨n,s,hi,hf,h⟩:= ih
       refine ⟨n+1,(Nat.casesOn (motive:=fun _=>X) · w s),rfl,hf,?_⟩
       intro i hv; cases i
       · exact (show R (s 0) w from hi.symm ▸ hh)
       next i=> exact h _ (by omega)

private lemma concatenate (H:ℕ→X→X→Prop) (need:ℕ→X→X→ℕ) (S:ℕ→ℕ) (h0:S 0=0)(hs:StrictMono S) (A:ℕ→ℕ→X)(hL:∀ k,A (k+1) (S (k+1))= A k (S (k+1)))
   (hx:∀ k i,S k≤ i→ i<S (k+1) → H k (A k (i+1)) (A k i) ∧ need k (A k (i+1)) (A k i) ≤ i+need 0 (A 0 1) (A 0 0)): Nonempty (Pavement H need) :=by
  let Within (k i:ℕ):Prop:= S k≤ i∧ i<S (k+1)
  have hu k: Within k (S k):= ⟨le_rfl, hs (by omega)⟩
  have he k i (hi: Within k i): Within k (i+1) ∨ (i+1=S (k+1) ∧ Within (k+1) (i+1)):=by
    obtain ⟨h,h'⟩:=hi
    obtain h|h:= lt_or_eq_of_le (show i+1≤S (k+1) from h'); exact Or.inl ⟨by omega,h⟩; exact Or.inr ⟨h,h.symm ▸ hu (k+1)⟩
  have hw i : ∃ k,Within k i:=by
       induction i with
       | zero=> exact ⟨0,(by simpa only [h0] using hu 0)⟩
       | succ i ih=> obtain ⟨k,hk⟩:=ih; exact Or.elim (he k i hk) (fun h=> ⟨k,h⟩) (fun h=>⟨k+1,h.2⟩)
  choose E hE using hw
  let U i:= A (E i) i
  have hz k i (hp:Within k i):E i=k:= by
      obtain ⟨ha,hb⟩:=hp; obtain ⟨hc,hd⟩:= hE i
      obtain h|h|h:=lt_trichotomy (E i) k; · have h:=hs.monotone (show E i+1≤k from h); omega
      · exact h
      have h:=hs.monotone (show k+1≤E i from h); omega
  have hP k i (hip:Within k i): U i= A k i∧ U (i+1)= A k (i+1) ∧ E i ≤ E (i+1) ∧ E (i+1)≤ E i+1:=by
       unfold U; rw [hz k i hip]; refine ⟨rfl,?_⟩
       obtain h|⟨h,h'⟩:= he k i hip
       · rw [hz _ _ h]; exact ⟨rfl,by omega,by omega⟩
       rw [hz _ _ h',h,hL]; exact ⟨rfl,by omega,le_rfl⟩
  have hh k:= hP _ _ (hE k); have hb:Within 0 0:=(by simpa only [h0] using hu 0)
  have hv k:H (E k) (U (k+1)) (U k) ∧ need (E k) (U (k+1)) (U k)≤ k+need 0 (U 1) (U 0):=by
     have ht:=hP _ _ hb; rw [(hh k).1,(hh k).2.1,ht.1,ht.2.1]; exact hx _ _ (hE k).1 (hE k).2
  have hm:Monotone E:=monotone_nat_of_le_succ fun i=>(hh i).2.2.1
  refine ⟨⟨E,U,fun i=>(hh i).2.2.1,fun i=>(hh i).2.2.2,hz _ _ hb, ?_,fun i=>(hv i).1,fun i=>(hv i).2⟩⟩
  refine tendsto_atTop.2 (fun k=>?_)
  filter_upwards [eventually_ge_atTop (S k)] with i hi; exact (hz (i:=S k) k (hu k)) ▸ hm hi

open Finset in
theorem deploy (H:ℕ→ X→X→Prop) (need:ℕ→X→X→ℕ) (hs:∀ i,Century (H i)): Nonempty (Pavement H need):=by
    classical
    choose T hT h using fun i=> hs i
    choose n V h0 hS hE using fun i=> view (h i (T (i+1)))
    let U i m:= need i (V i (m+1)) (V i m)
    let W i:= need i (T i) (T i)
    let p i:= W (i+1)+(Finset.range (n i)).sum (U i)+1
    have hp i:0<p i:=by unfold p; positivity
    let R i:= (Finset.range i).sum fun j=> p j+n j
    have hR:R 0=0:=by simp[R];
    have hF i: R (i+1)=R i+p i+n i:=by unfold R; simp only [Finset.sum_range_succ, Nat.add_assoc]
    have hh : StrictMono R:= strictMono_nat_of_lt_succ fun i=> by have h:= hp i; rw [hF]; omega
    let Z i:=R i+p i
    let A k j := V k (j-Z k)
    have hA k : A k (R k)=T k:=by unfold A Z; rw [Nat.sub_eq_zero_of_le (by omega),h0]
    have ht k: R (k+1)=Z k+n k:=hF k
    have hy k: A k (R (k+1))=T (k+1):=by unfold A; rw [ht,Nat.add_sub_cancel_left,hS]
    apply concatenate H need R hR hh A (by intro k; rw [hA,hy])
    intro k i hk hi; have hK: A 0 0=T 0:=hR ▸ hA 0
    have hL:1 ≤Z 0:=le_add_left (hp 0)
    rw [hK,show A 0 1=T 0 from (show _=_ from by unfold A; rw [Nat.sub_eq_zero_of_le hL,h0])]; rw [ht] at hi
    by_cases he:i<Z k
    · unfold A; rw [Nat.sub_eq_zero_of_le he,Nat.sub_eq_zero_of_le he.le,h0]; refine ⟨hT k,?_⟩
      change W k≤ i+W 0
      cases k with
      | zero=> omega
      | succ k=>
          rw [hF] at hk; have h:W (k+1) ≤ p k:=by unfold p; omega
          omega
    have hW: Z k ≤ i:=Nat.le_of_not_lt he; have hm:i-Z k<n k:=by omega
    have hg: A k (i+1)= V k (i-Z k+1):=by unfold A; rw [show i+1-Z k=i-Z k+1 by omega]
    rw [hg]; refine ⟨hE k _ hm,?_⟩; change U k (i-Z k) ≤ i+W 0
    have hl: U k (i-Z k) ≤ p k:=by
         apply le_trans (b:= ∑ i∈Finset.range (n k), U k i)
         · exact single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr hm)
         change ((Finset.range (n k)).sum (U k)) ≤ _; unfold p; omega
    unfold Z at hW; omega
end YM.Massive.Stratum
#print axioms YM.Massive.Stratum.deploy
