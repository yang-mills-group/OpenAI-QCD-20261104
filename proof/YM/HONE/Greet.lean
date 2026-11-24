import YM.HONE.Mills
import YM.Intag.Cavity
import YM.Intag.Mint
import YM.TIPS.Reg
/-! # Hypothesis checkout. Supports for arbitrary aperture blast at projected LifeT. HΩ all. No alignment oracle. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox QCD.Lat QCD.Grass MassiveQCD MassiveQCD.Cupola
open scoped BigOperators Classical
namespace CardsT
open Pilgrim Tess Column Finset Plum
variable {S:Scheme}{R:Side}{k i ℓ p n:ℕ}(A:Massive.Run S n R 6)
variable {I:Type}[Fintype I] (X:I→ Cover) (Q:I→Insertion (S.side R k) 6)
local notation "Z"=> S.side R
variable (u:I → Cover → Insertion (S.side R k) 6)
-- universal wire from radius.A.M ≤ φ_π. z footprints enough.S cost uses itinerary.E weight check Unit.
variable (hi:ℓ ≤ k)(hm:k ≤ n)
variable (M r t:ℕ)(h:∀ j:I,∀ x:Cover, Plum.Fence (window (wrap (S.side R k) x) (r+1)) (u j x))
local notation "Φ" k:arg=> Hole I S ℓ k
noncomputable def addressT(v:Φ k) (j:ℕ): Set (Site (S.side R j)):= Column.dome S R k (wrap (S.side R k) (showX S ℓ k X v)) M j
local notation "P"=> addressT (R:=R) X M (k:=k) (ℓ:=ℓ)
local notation "G"=> showX S ℓ k X
include h
lemma spotT (hx:r+1+50*(S.J k+10) ≤ M)(v:Φ k): Plum.Fence (P v k) (chordR (ℓ:=ℓ) X u v):=by
    have ht:=h v.1 (showX S ℓ k X v); apply ht.high; unfold addressT Column.dome; rw [homes S R]; refine Column.enlarg ?_; unfold allowance; rw [Column.home_c,one_mul]; omega
omit h
lemma validL (hx:50*(S.J k+10) ≤ M)(v:Φ k): Lease k n (P v):= leaseX S R (wrap (S.side R k) (G v)) M hx
-- any dispersed at ℓ > for hX support & Ep work. separate ancestry at Ω.all
include hi
lemma crater (hx:2*M < ratioTo S k ℓ * (t+2))(he:∀ u v,u≠v→ 202+t ≤ separation (wrap (Z ℓ) (X u)) (wrap (Z ℓ) (X v))) (j:ℕ)(hp:k ≤ j)(u v:Φ k)(ht:u.1≠v.1) : Disjoint (P u j) (P v j):= Column.battered _ _ _ _ _ (hx.trans_le (CardsT.zone _ _ ℓ k X t hi he _ _ ht)) hp
-- Hom travels through average recipe
omit hi
variable (Ux:I→Averaging) (w:I→Bool)(he:∀ t:I,∀ b V,Grass.Hom (w t) (u t b V))
local notation "d!"=> earnL S ℓ k i X Ux
include he
lemma expert (hp:i ≤ k)(hm:ℓ ≤ i)(v:Φ i)(V:Grid _): Hom (w v.1) (earnL S ℓ k i X Ux u v V):=by
       induction hp using Nat.decreasingInduction with
       | self=> rw [receive]; exact he ..
       | of_succ i hi ih=>
           obtain ⟨g,h⟩:= allS S ℓ i X Ux hm; let j:=i+1
           rw [towers S ℓ k i X Ux g h u hi v, ContinuousMap.sum_apply]; apply QCD.Grass.Hom.sum; intro x hx -- name
           rw [show v.1=x.val.1 from x.property.1.symm]; exact (ih (Nat.le_succ_of_le hm) _).smul _ -- coe real
-- root BV Potion. prove on any ℓ.Hot.T periods hft. ancient Legend
variable (F:I → Cover → Insertion (S.side R n) 6)(hF:∀ t:I,∀ b V,Grass.Hom (w t) (F t b V))
include hi hm hF
lemma coatingT (v:Φ ℓ)(V: Grid (S.side R n)): Hom (w v.1) ((doubleT A X Ux F u v) V):=by
    unfold doubleT; change Hom _ ((earnL S ℓ k ℓ X Ux (fun t x=>climbH A k n (u t x)) v) V + (- earnL S ℓ n ℓ X Ux F v V)); apply Grass.Hom.add
    · have h : ∀ i:ℕ,ℓ ≤ i→ i ≤ k→∀ v:Φ i,Hom (w v.1) ((earnL S ℓ k i X Ux (fun t x=>climbH A k n (u t x)) v) V):=by
          intro i h hδ; induction hδ using Nat.decreasingInduction with
          | self=> intro u'; rw [receive]; exact Lyre.steep A _ _ (stays (ContinuousMap.continuous _)) (he _ _) hm V
          | of_succ i ht ih=> intro v; obtain ⟨g,hg⟩:= allS S ℓ i X Ux h; rw[towers S ℓ k i X Ux g hg _ ht, Finset.sum_apply]; apply QCD.Grass.Hom.sum; intro x hx; rw [show v.1=x.val.1 from x.property.1.symm]; exact (ih (Nat.le_succ_of_le h) _).smul _
      exact h _ le_rfl hi _
    have ht:= expert X F Ux w hF (hi.trans hm) le_rfl v V; rw [← neg_one_smul ℂ]; exact ht.smul _
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.spotT
#print axioms YM.Intag.CardsT.validL
#print axioms YM.Intag.CardsT.crater
#print axioms YM.Intag.CardsT.coatingT
