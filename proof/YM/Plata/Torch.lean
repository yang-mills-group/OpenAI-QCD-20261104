import YM.Plata.Loans
/-! At every fixed epoch, root polynomial costs quantify EACH phase.
Since oracle spends after each requests, preserves growth freedom for arbitrary derivatives. -/
set_option maxHeartbeats 800000
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
variable {D k n m:ℕ}
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola
open Quills.Clover YM.Arise.Bill YM.Arise.Count Play Play.Chamber
variable (X:Fin n→ Glyph D) (A:Compass C D)(x:Fin n→ Cover)
variable (V: Legend) (Z:ℕ→ Legend) (T:List (Fin n)) (R:Bankroll P φ Q S)
set_option quotPrecheck false
local notation "xQ" => A.qR A.ℓ ∘ x
-- Fused prices.Fin.S
noncomputable abbrev premium (X:Fin n→ Glyph D) (y:Points n):ℝ:= ∑ i∈cutS n, ‖saves (weightsT X) (menuP X) (codes X) y.ofLp (id:Fin n→Fin n) i‖
variable (hx:∀ i,X i∈ A.Ω)(hX:∀ i,(X i).material≠0)(hK:n≤ A.K)(hp:A.qR A.ℓ ∘ x∈ flats (Fin n) (2*A.e) (A.v/2))(hA:Known A)
include hx hX hK hp hA R
lemma impress (hc:Pod P A φ V): let y:= A.qR A.ℓ ∘ x; ‖S n (A.r • points y) (fun i=>choiceT V Q (X i).material)-candle X y‖ ≤ premium X (points y)* A.bid:=by
        obtain ⟨g,Z,hf,hg,hV⟩:= hc.proc; let z:= A.qR A.ℓ ∘ x; have hu:Injective z:= noCol _ _ z hp (mul_pos (by norm_num) hA.live)
        have ht:= itemized X A x V Z R g hu hx hX hK hp hA hf.tendsto_atTop hg hV; intro y
        unfold pebG lumps at ht; rw [positionK,counter] at ht; rw [show S n (A.r • points y) (fun i=> choiceT V Q (X i).material)= candle X y+ _ from ht,add_sub_cancel_left,premium,Finset.sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i hi=>?_); rw [norm_mul]; exact mul_le_mul_of_nonneg_left (chargedM X A x V Z R g hu hx hX hK hp hA hf.tendsto_atTop hg hV ⟨i,hi⟩) (norm_nonneg _)
omit R hx hX hp hK hA
open Vale Canopy
variable (E: Canopy P φ Q)
lemma stepP (K:Set (Points n))(hk:K ⊆ conf n):ContinuousOn (premium X) K:=by
       apply continuousOn_finsetSum; intro i hi
       have hu:i⊆Quills.crest (id:Fin n→Fin n):= mem_powerset.mp (mem_of_mem_erase hi)
       intro x hx; have h:Injective x.ofLp:=hk hx; refine (ContinuousAt.norm ?_).continuousWithinAt
       exact (Quills.Pulp.enhance (weightsT X) (menuP X) (codes X) x.ofLp i id h.injOn hu).comp ((PiLp.continuous_ofLp ..).continuousAt)
lemma immutable (x:Fin n→ Texts)(i j:ℕ)(h:∀ l:Fin n,(x l).1≤ i)(H:∀ l:Fin n,(x l).1≤ j): premium (fun l=>GlyphV (x l).2 i (h l))=premium (fun l=>GlyphV (x l).2 j (H l)):=by rfl -- source board may same.H
include R
lemma tours: Troupe E S:=by
      constructor; intro n t ht K hk h q ε he
      have hC:= copperP E t ht; obtain ⟨i,u,-⟩:= hC.exists; let Tz(j):= GlyphV (t j).2 (E.Pz i) (u j)
      obtain ⟨C,hQ⟩:= (hk.image_of_continuousOn (stepP Tz K h)).bddAbove
      have hz:Tendsto (fun k=> E.cc k^q*(E.B k).bid*C) atTop (𝓝 0):= by simpa only [zero_mul] using (E.shots q).mul_const C
      filter_upwards [E.care K hk h 2 (1/2) (by norm_num) (by norm_num), E.many.eventually_ge_atTop n,hz.eventually_le_const he,hC] with j h1 h2 h3 h4
      intro l f y hs; obtain ⟨v,hv⟩:=h4; let X(i:Fin n):=GlyphV (t i).2 (E.Pz j) (v i); have hX(i): (X i).material≠0:=(ht i).1
      have hu:l.qR l.ℓ ∘ f∈ flats (Fin n) (2*l.e) (l.v/2):=by rw[show l.v/2= (1/2)*l.v from (by ring)]; have hh:= h1 (a:=y) hs; exact hh
      have hp:= impress X l f (E.V j) R hv hX h2 hu (E.trueK j) (E.checkedW j).legit; have h' : premium X y ≤ C:=by
           rw [show premium X=premium Tz from immutable t (E.Pz j) (E.Pz i) v u]; exact hQ ⟨_,hs,rfl⟩
      have hx: ‖errorP E S t j y‖≤ C*l.bid:= (show ‖errorP E S t j y‖ ≤ premium X y * l.bid from hp).trans (mul_le_mul_of_nonneg_right h' (Ibis.grow ..).le)
      exact (mul_le_mul_of_nonneg_left hx (pow_nonneg (zero_le_one.trans (E.charge j)) _)).trans (by rw[mul_comm C, ←mul_assoc]; exact h3)
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.tours
