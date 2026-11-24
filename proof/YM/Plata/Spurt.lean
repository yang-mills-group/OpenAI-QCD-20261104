import YM.Plata.Dingy
/-! Use all subword corrections on the SAME cutoff station. -/
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
variable (X:Fin n→ Glyph D) (A:Compass C D)(x:Fin n→ Cover)
variable (p:Fin n→ E4) (V: Legend) (Z:ℕ→ Legend) (T:List (Fin n)) (f:ℕ→ℕ)
set_option quotPrecheck false
local notation "W" i:arg => Z (f i)
local notation "Q₀" => weightsT X
local notation "u₀" => menuP X
local notation "VZ" => codes X
local notation "xQ" => A.qR A.ℓ ∘ x
local notation "LZ" k:arg=>C.S.side (C.R (f k)) (C.N (f k))
local notation "uV" => (univ:Finset (Fin n))
noncomputable abbrev crestit (n:ℕ): Finset (Fin n):= crest (id:Fin n→ Fin n)
noncomputable abbrev substr (q:Finset (Fin n)):= crestit n\q
noncomputable abbrev lensR (q:Finset (Fin n)):= List.ofFn (tour (substr q))
noncomputable abbrev cutS (n:ℕ): Finset (Finset (Fin n)):= (crestit n).powerset.erase (crestit n)
noncomputable abbrev Ears (n:ℕ):= ↥(cutS n)
lemma clim {q:Ears n}: 0< (substr q.val).card:=card_pos.mpr (sdiff_nonempty.mpr (fun h=> ne_of_mem_erase q.property ((mem_powerset.mp (mem_of_mem_erase q.property)).antisymm h)))
noncomputable abbrev again (q:Finset (Fin n)):= saves (weightsT X) (menuP X) (codes X) (A.qR A.ℓ ∘ x) (id:Fin n→ Fin n) q
noncomputable abbrev nesting(n:ℕ):= Σ i:Ears n, ↥(bunch (lensR i.val))
noncomputable abbrev Funnel(n:ℕ):= Unit ⊕ nesting n
noncomputable abbrev UI (u:Funnel n): List Bond:= Sum.elim (fun _=>[]) (fun q=> SpreadW X A x V Z f q.snd.val) u
noncomputable abbrev CK:ℂ:= Ibis.candle X (A.qR A.ℓ ∘ x)
noncomputable abbrev Ut (u:Funnel n):ℂ:= Sum.elim (fun _=> CK X A x) (fun q=> again X A x q.fst.val*fPrint X A x (lensR q.fst.val) q.snd.val) u
noncomputable abbrev lumps := poisedP A Z f V X (A.qR A.ℓ ∘ x) (cave A x)
variable (he:Injective (A.qR A.ℓ ∘ x))
include he
set_option maxHeartbeats 560000
lemma cleft (k:ℕ)(h:∀ i V',Hom (weightsT X i) (literalK (P:=P) X A x Z (f k) i V')): task P (f k) (wade (lumps X A x V Z f) k)=Klay (P:=P) (UI X A x V Z f) (Ut X A x) f k :=by
       let y:= literalK (P:=P) X A x Z (f k)
       have hm:= Sworn.literal Q₀ y h u₀  (xQ) (id:Fin n→Fin n) VZ he.injOn injective_id
       -- simplify RHS sums before compare
       let c(i:Finset (Fin n)):= funded (P:=P) X A x V Z (lensR i) f k
       let g(i:Finset (Fin n)):= again X A x i • c i
       have hp:Klay (P:=P) (UI X A x V Z f) (Ut X A x) f k= (CK X A x • 1)+∑ i∈ cutS n,g i:=by
            unfold Klay cash; rw [Fintype.sum_sum_type]; rw [←sum_coe_sort (cutS n) g] -- dummy
            simp only [Finset.univ_unique,Finset.sum_singleton]; apply congr_arg₂ (·+·)
            · simp only [UI,Ut,Sum.elim_inl,wade,List.map_nil,task,List.prod_nil]
            rw[Fintype.sum_sigma]; refine Finset.sum_congr rfl fun i _=>?_; unfold g c funded Klay cash; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _=>by rw [smul_smul]; rfl
       rw [hp]; apply DFunLike.coe_injective; let Fp:= (fun i:Fin n=> treeX P (f k) (Z (f k)) X (cave A x (f k)) i)
       have he': ((List.ofFn (y∘(id:Fin n→Fin n))).prod)=(⇑((List.ofFn Fp).prod)):=by rw [List.ofFn_eq_map,List.ofFn_eq_map,Plata.coed]; rfl
       unfold lumps; rw[fits,← show _= _ from he',hm]; change _=⇑(_ + ∑ i∈ _,g i); rw [ContinuousMap.coe_add,coeF (C:=C) (f k)]
       apply congr_arg₂ (·+·)
       · suffices F': CK X A x = UV.Free.moment (u₀ ∘ id) (points ( (xQ) ∘ id)) (fun i=> meaning _ _ (codes X ((id:Fin n→Fin n) i))) by apply Eq.symm; rw [F']; rfl -- orientation
         apply congr_arg (UV.Free.moment (u₀) (points (xQ))); exact funext fun i=> (Hymnal.impetus ..).symm
       refine Finset.sum_congr (by unfold cutS crestit; ext v; simp) fun i hi=>?_ ; unfold g; rw[ContinuousMap.coe_smul]
       -- coe figure with two decidable_eq Fin.n
       apply congr_arg (again X A x i • ·); let G:=lensR i; have ht:G.Nodup:= List.nodup_ofFn.mpr (snug _)
       apply Eq.trans (?_) (ink X A x V Z G f ht he k h); apply congr_arg (Sworn.readL Q₀ · u₀  (xQ) VZ y h) ?_; refine congr_arg (fun v:Finset (Fin n)=> List.ofFn (tour v)) ?_; unfold substr crestit; ext j; simp
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.cleft
