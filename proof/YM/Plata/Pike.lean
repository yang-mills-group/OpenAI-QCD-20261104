import YM.Plata.Unders
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
open YM.Plata Function Metric Set Finset
namespace Compass
open Choir Strip
variable {Q:Choir}{C:Sequence}{P: Calibration C}{φ:ℕ→ℕ}{S:Canopy.KForm Q}
variable (R:Bankroll P φ Q S){p D k n:ℕ}
lemma nullProvision {k:ℕ}{β ε:ℝ}(hp:C.Path β ε): Spans k (C:=C) 0 1 1 0:=by
     let T:= Column.sky C.S (C.R k) 0 (C.N k) (Nat.zero_le _) (evenW _ _ (hp.even k) _) (0:Site (C.S.side (C.R k) 0)); have he:C.S.spacing (C.N k)*T.side.val=1:=(footprint C.S 0 (C.N k) (Nat.zero_le _)).trans (C.S.spacing_zero); let y:T.Cell:=0
     refine ⟨T,(fun _=>y), (fun _=>0),rfl,he,injective_of_subsingleton _,(fun i=>⟨?_ ,false,?_⟩),?_,?_⟩
     · have hh:= Fence.mass (Fence.one (F:=6) (A:=T.chamber y)) 0; simpa only [zero_smul] using hh
     · intro H; change Hom false 0; simp[Hom,Plus]
     · let ht:= top_spin T (C.A k).regulator y (0:Stud (C.S.side (C.R k) (C.N k)) 6) 0 ; rw [zero_smul] at ht; rw [Fin.prod_univ_one,ht]; simp
     simp -- Coe
variable {I J:Type} [Fintype I][Fintype J]
variable (x:I→ List Bond)(y:J→List Bond)(z:I→ℂ)(v:J→ ℂ)
noncomputable abbrev Klay (f:ℕ→ℕ)(i:ℕ):= cash P (f i) (fun j=> wade (x j) i) z
noncomputable abbrev feek (S:Canopy.KForm Q)(x:I→List Bond)(z:I→ℂ):= ∑ j:I,z j*pebG Q S (x j)
include R
lemma worth (f:ℕ→ℕ)(h:Tendsto f atTop atTop)(hx:∀ i,Strip.distinct (Plata.position (Q:=Q) (x i)))(hy:∀ i,Worn C (φ∘f) (x i))(hX:∀ i,Strip.distinct (Plata.position (Q:=Q) (y i)))(hY:∀ i,Worn C (φ∘f) (y i))(hz:∀ᶠ i in atTop,Klay (P:=P) x z (φ∘f) i=Klay (P:=P) y v (φ ∘f) i): feek S x z=feek S y v:=by
      let W:I ⊕ J→ ℂ:= Sum.elim z (fun i=> -v i); let l:I ⊕ J→ List Bond:= Sum.elim x y
      have hQ:∀ i,Strip.distinct (Plata.position (Q:=Q) (l i)):= Sum.rec (hx) (hX); have hV:∀ i,Worn C (φ∘f) (l i):= Sum.rec hy hY
      obtain ⟨β,e,he⟩:=R.path; have hp:=R.here l W 1 f hQ h (?_ : Available P (φ∘f) l W 0 1 1) hV le_rfl zero_lt_one; swap
      · filter_upwards [hz] with i hi; unfold cash; rw [Fintype.sum_sum_type]; change Spans _ (C:=C) (Klay x z _ _ + ∑ j:J, (-v j) • task P ((φ∘f) i) (wade (y j) i)) _ _ _; rw[hi]; simp only[Klay,cash,neg_smul,Finset.sum_neg_distrib,add_neg_cancel]; exact nullProvision he
      apply sub_eq_zero.mp; have ht:feek S l W=0:= norm_le_zero_iff.mp hp; rw [feek,Fintype.sum_sum_type] at ht; change feek S x z+ ∑ i:J, -v i*pebG Q S (y i) =0 at ht; rw [sub_eq_add_neg]; unfold feek; simpa only [feek,neg_mul,sum_neg_distrib] using ht
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.worth
