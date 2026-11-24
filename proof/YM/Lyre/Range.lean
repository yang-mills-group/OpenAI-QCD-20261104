import YM.Lyre.Towers
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open Transfer
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical
variable {S:Scheme}{R:Side}{N F i j:ℕ}(A:Run S N R F)
local notation "f"=> S.side R
local notation "P" k=> S.step k
lemma stocked (x:Stud (f i) F)(t:ℂ)(h:i≤j) : climbH A i j (t • x)=t • climbH A i j x:=by
    induction h using Nat.decreasingInduction with| self=>rw [same,same]| of_succ k hk ih=> rw [Lyre.next _ _ hk, retreat, ih, ← Lyre.next _ _ hk]
lemma squads (x y:Stud (f i) F)(hx:Stays x)(hy:Stays y)(h:i≤j): climbH A i j (x+y)=climbH A i j x+climbH A i j y:=by
    induction h using Nat.decreasingInduction with
    | self=> rw [same,same,same]
    | of_succ k hk ih=> rw [Lyre.next _ _ hk,Lyre.next _ x hk,Lyre.next _ y hk, retreats A x y hx hy]; exact ih _ _ (retractS _ x hx) (retractS _ y hy)
lemma funded_one (h:i≤j) :climbH A i j 1=1:=by induction h using Nat.decreasingInduction with| self=> rw [same]| of_succ k hk ih=> rw [Lyre.next _ _ hk,retract_one,ih]
lemma funded_zero (h:i≤j):climbH A i j 0=0:=by have hz:=stocked A (0:Stud (f i) F) 0 h; simpa using hz
variable (X Y:∀ i,Set (Site (S.side R i)))
private abbrev okC (X: ∀ n,Set (Site (f n))) (i j:ℕ) := ∀ k:ℕ, i≤k → k<j → ∀ z∈ X k, Push.GridApprox.window ((QCD.Flume.sliceL (P k) (S.sides_next R k)).embed z) (Tide.fuel (P k).patch) ⊆ X (k+1)
def Lease (i j:ℕ) (X: ∀ k, Set (Site (f k))) := okC X i j
lemma steps (H: Lease i j X)(x:Stud (f i) F)(hx:Plum.Fence (X i) x)(h:i≤ j): Plum.Fence (X j) (climbH A i j x):=by
    induction h using Nat.decreasingInduction with
    | self=> rw [same]; exact hx
    | of_succ k hk ih => rw [Lyre.next _ _ hk]; exact ih (fun j hj=>H j (by omega)) _ (retractF A _ _ _ hx (H _ le_rfl hk))
lemma parted (H:Lease i j X)(E:Lease i j Y)(W:∀ k:ℕ,i≤k → k<j → Disjoint (X k) (Y k)) (x y: Stud (f i) F)(hx:Plum.Fence (X i) x)(hy:Plum.Fence (Y i) y)(h:i≤j):climbH A i j (x*y)=climbH A i j x* climbH A i j y:=by
    induction h using Nat.decreasingInduction with
    | self=> rw [same,same,same]
    | of_succ k hk ih=>rw [Lyre.next _ _ hk,Lyre.next _ x hk,Lyre.next _ y hk,retract_mult A (X k) (Y k) _ _ hx hy (W _ le_rfl hk)]; exact ih (fun j hj=>H j (by omega)) (fun j hj=>E j (by omega)) (fun j hj=>W j (by omega)) _ _ (retractF A _ _ _ hx (H _ le_rfl hk)) (retractF A _ _ _ hy (E _ le_rfl hk))
-- list prices, including all simultaneously FULL
variable {I:Type*}[Fintype I](l:List I)(X0:I→ ∀ k,Set (Site (S.side R k))) (x:I→Stud (S.side R i) F)
omit [Fintype I] in
lemma housed (hx:∀ p∈l,Plum.Fence (X0 p i) (x p)): Plum.Fence (⋃ p∈l,X0 p i) (l.map x).prod :=by
    induction l with
    | nil=> exact Plum.Fence.one
    | cons a l ih=>
       refine ((hx a (by simp)).high ?_).mult ((ih fun p hp=> hx p (List.mem_cons_of_mem a hp)).high ?_)
       · exact Set.subset_iUnion_of_subset a (Set.subset_iUnion (fun _ : a∈a::l=>X0 a i) (by simp))
       apply Set.iUnion_subset; intro p; apply Set.iUnion_subset; intro hp; exact Set.subset_iUnion_of_subset p (Set.subset_iUnion (fun _:p∈a::l=>X0 p i) (List.mem_cons_of_mem a hp))
lemma pieces (hx:∀ p∈l,Plum.Fence (X0 p i) (x p))(hv:∀ p∈l,Lease i j (X0 p))(hn:l.Nodup)(he: ∀ k:ℕ,i≤k → k<j → ∀ p∈l,∀ s∈l,p≠ s→Disjoint (X0 p k) (X0 s k))(h:i≤j): climbH A i j (l.map x).prod= (l.map fun p=>climbH A i j (x p)).prod:=by
    induction l with
    | nil=> exact funded_one A h
    | cons a l ih=>
       let M(k):=⋃ p∈l,X0 p k; have hL(p)(hp:p∈l):p∈a::l:= List.mem_cons_of_mem _ hp
       have hV : Lease i j M:=by intro k hu ht x hx'; obtain ⟨p,hp⟩:=Set.mem_iUnion.1 hx'; obtain ⟨hq,hp⟩:=Set.mem_iUnion.1 hp; exact (hv p (hL p hq) k hu ht x hp).trans (Set.subset_iUnion_of_subset p (Set.subset_iUnion (fun _ : p∈l=> X0 p (k+1)) hq))
       have hM(k) (hr:i≤k)(ht:k<j):Disjoint (X0 a k) (M k):=by
            apply Set.disjoint_left.2; intro y hy hy'; obtain ⟨p,hp⟩:=Set.mem_iUnion.1 hy'; obtain ⟨hv,hp⟩:=Set.mem_iUnion.1 hp; exact Set.disjoint_left.mp (he k hr ht a (by simp) p (hL p hv) (fun h=>(List.nodup_cons.mp hn).1 (h.symm ▸ hv))) hy hp
       simp only [List.map_cons,List.prod_cons]; rw [parted A _ M (hv a (by simp)) hV hM _ _ (hx a (by simp)) (housed _ _ _ (fun _ hp=>hx _ (hL _ hp))) h, ih (fun p hp=>hx p (hL p hp)) (fun p hp=>hv p (hL p hp)) (List.nodup_cons.mp hn).2 (fun k hk hj p hp s hs=> he k hk hj p (hL p hp) s (hL s hs))]

-- reflection intertwining
lemma retractR (C:Cells.Cut (f i))(x:Stud (f i) F)(hp:Stays x)(ht:C.kind=.link): tallH (gateH C (QCD.Flume.sliceL (P i) (S.sides_next R i))) (retract A i x)=retract A i (tallH C x):=by
     unfold retract; rw [utter _ _ (S.admissible i) _ (paysA x hp) ht,stage]
lemma full_tall(C:∀ k,Cells.Cut (S.side R k)) (u: Stud (f i) F)(hp:Stays u)(ht:(C i).kind=.link)(hf:∀ k:ℕ,i≤ k→ k<j→ C (k+1)=gateH (C k) (QCD.Flume.sliceL (S.step k) (S.sides_next R k)))(h:i≤j) : tallH (C j) (climbH A i j u)= climbH A i j (tallH (C i) u):=by
     induction h using Nat.decreasingInduction with | self=> rw [same,same] | of_succ k hk ih=>
        have hR:=hf k le_rfl hk; rw [Lyre.next _ _ hk,Lyre.next _ (tallH _ _) hk]; rw [← retractR _ _ u hp ht,← hR]; exact ih _ (retractS _ u hp) (by rw [hR]; rfl) (fun j hj=>hf j (by omega))
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.pieces
#print axioms YM.Massive.Lyre.full_tall
