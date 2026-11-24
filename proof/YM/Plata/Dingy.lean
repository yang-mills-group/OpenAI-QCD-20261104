import YM.Plata.Pike
/-!
ProbeWords on any sublist by literal transfer with same Z. Lift to insertion
with linear (signed) polynomial. -/
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
variable {Q:Choir}{C:Sequence}{P: Calibration C}{S:Canopy.KForm Q}
variable {D k n m:ℕ}
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola
open Quills.Clover YM.Arise.Bill YM.Arise.Count Play Play.Chamber
open Goblet
variable (X:Fin n→ Glyph D) (A:Compass C D)(x:Fin n→ Cover)
variable (p:Fin n→ E4) (V: Legend) (Z:ℕ→ Legend)
variable (T:List (Fin n)) (f:ℕ→ℕ)
set_option quotPrecheck false
local notation "W" i:arg => Z (f i)
local notation "Q₀" => weightsT X
local notation "u₀" => menuP X
local notation "VZ" => codes X
local notation "xQ" => A.qR A.ℓ ∘ x
local notation "LZ" k:arg=>C.S.side (C.R (f k)) (C.N (f k))
noncomputable abbrev cave (k:ℕ):= A.hike k ∘ x
noncomputable abbrev room (i:Fin n):= markedG A Z f V X (A.qR A.ℓ ∘ x) (fun i:ℕ=> A.hike i ∘ x) i -- directory
noncomputable abbrev Tent (l:List (Fin n)):=l.map (room X A x V Z f)
noncomputable abbrev SpreadW (q:Finset (Fin n)):= Tent X A x V Z f (List.ofFn (tour q))
noncomputable abbrev bunch:= T.toFinset.powerset
noncomputable abbrev fPrint(q:Finset (Fin n)):= compZ (weightsT X) (menuP X) (codes X) (A.qR A.ℓ ∘ x) T q
noncomputable abbrev waveW (k:ℕ):=treeX P k (Z k) X (cave A x k)
noncomputable abbrev literalK (k:ℕ) (q:Fin n): Stud (C.S.side (C.R k) (C.N k)) 6:=checkW P A k (Z k) X x q
lemma pocketP (v:List (Fin n))(k:ℕ): task P (f k) (wade (Tent X A x V Z f v) k)=(v.map (waveW (P:=P) X A x Z (f k))).prod:=by unfold task wade Tent; rw [List.map_map,List.map_map]; rfl
noncomputable abbrev funded (k:ℕ):= Klay (P:=P) (fun i: ↥(bunch T)=> SpreadW X A x V Z f i.val) (fun i=> fPrint X A x T i.val) f k
lemma coeF (k:ℕ){X: Finset (Fin n)→ Insertion (C.S.side (C.R k) (C.N k)) 6}(u:Finset (Finset (Fin n))): ⇑(∑ i∈u,X i) = ∑ i∈u,⇑(X i):=by induction u using Finset.induction_on with|empty => simp| insert i u hi ih=> simp only[sum_insert hi,ContinuousMap.coe_add,ih]
lemma ink (hn:T.Nodup)(he:Injective (A.qR A.ℓ ∘ x))(k:ℕ)(h:∀ i V',Hom (weightsT X i) (literalK (P:=P) X A x Z (f k) i V')): ProbeWords X T (A.qR A.ℓ ∘ x) (literalK (P:=P) X A x Z (f k)) h= ⇑(funded (P:=P) X A x V Z T f k):=by
       have hm:=Sworn.featured (weightsT X) (literalK (P:=P) X A x Z (f k)) h T (menuP X) (A.qR A.ℓ ∘ x) (codes X) hn he.injOn; let B(i: Finset (Fin n)):= fPrint X A x T i • task P (f k) (wade (SpreadW X A x V Z f i) k); rw [show funded (P:=P) X A x V Z T f k=∑ i∈bunch T,B i from (Finset.sum_coe_sort _ B)]; rw [coeF]; apply hm.trans; refine Finset.sum_congr (by ext v; simp [bunch,Finset.subset_iff]) fun i hi=>?_; change _=⇑(fPrint X A x T i • task P (f k) (wade (Tent X A x V Z f (List.ofFn (tour i))) k)); rw [pocketP, ContinuousMap.coe_smul, Plata.coed]; congr 1; unfold Sworn.betaX; rw[List.map_ofFn]
variable (hV:Known A)(hu:Injective (A.qR A.ℓ ∘ x))(hx:∀ i,X i∈ A.Ω)(hX:∀ i,(X i).material≠0)(hK:n≤ A.K)(hp:A.qR A.ℓ ∘ x∈ flats (Fin n) (2*A.e) (A.v/2))
local notation "Ri" j:arg=> (C.A (f j)).regulator
-- renumbering applies in Grass.Faith via lemma figure.H
variable (g:Fin m→Fin n)(ht:Injective g)
local notation "gL"=> List.ofFn g
include hx hu hX hK hp ht
set_option maxHeartbeats 550000
lemma doles (k:ℕ)(he:Plot P A (f k) (Z (f k)))(hy:0 < m): Spans (C:=C) (f k) (funded (P:=P) X A x V Z (List.ofFn g) f k) 1 (C.S.spacing A.pA) A.bid:=by
       let u:= A.qR A.ℓ ∘ x; let Y:= checkW P A (f k) (W k) X x; have hv : m≤n:=by simpa using Fintype.card_le_of_injective g ht
       have ht': u∘g∈ flats (Fin m) (2*A.e) (A.v/2):=by
             obtain ⟨h1,h2⟩:= (outward _ _ _).1 hp; apply (outward ..).2
             have hh: ‖u ∘ g‖≤ ‖u‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i=> norm_le_pi_norm u (g i)); exact ⟨hh.trans h1,fun i j hi=> h2 _ _ (ht.ne hi)⟩
       let W':= checkW P A (f k) (W k) (X ∘g) (x ∘g)
       let L:= List.finRange m
       obtain ⟨p,hZ,htQ,hY,H,Ht⟩:=he.proofH m (X∘g) (fun i=> hx _) (fun i=> hX _) (hv.trans hK) hy (x∘g) ht'
       obtain ⟨-,_,_,hq,HL⟩:= he.proofH n X hx hX hK (hy.trans_le hv) x hp -- unused for each parity
       let Tf:= Column.sky C.S (C.R (f k)) A.pA (C.N (f k)) hZ (evenW _ _ htQ _) p; let z:= ProbeWords X (List.ofFn g) u Y hq; let a:Tf.Cell:=0;
       have hh:z= ProbeWords (X∘ g) L (u∘g) W' hY:=by
          let F:Fin m↪ Fin n:=⟨g,ht⟩; funext U; apply Eq.trans ?_ (Quills.Clover.figure (weightsT (X∘g)) (weightsT X) F (fun i=>rfl) (menuP X) (codes (X∘g)) (codes X) (u∘ g) u L.toFinset ((hu.comp ht).injOn) (fun _ _=> rfl) (fun _ _=> rfl) (fun i=> W' i U) (fun j=>Y j U) (fun i=> hY i U) (fun i=>hq i U) L (by congr; exact Subsingleton.elim .. ) (fun i _=>rfl) (List.nodup_finRange _)); unfold z ProbeWords; rw[show List.ofFn g= L.map F from List.ofFn_eq_map ..]; rfl
       have hF: Potion z∧ topH Tf (Ri k) z a ≤ A.bid:= by rw [hh]; exact Ht
       refine ⟨Tf,(fun _:Fin 1=> a),(fun _:Fin 1=>z),rfl,footprint C.S _ _ hZ,injective_of_subsingleton _,(fun _=> ⟨hh ▸ H,hF.1⟩),?_,?_⟩; · rw [Fin.prod_univ_one]; exact hF.2
       rw [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]; exact ink X A x V Z (List.ofFn g) f (List.nodup_ofFn.mpr ht) hu k hq
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.doles
