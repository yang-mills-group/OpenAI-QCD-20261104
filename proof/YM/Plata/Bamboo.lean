import YM.Plata.Bronze
import YM.Sprig.DialP
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
variable {Q:Choir}{C:Sequence}{P:Calibration C}{k n D:ℕ}
-- core uses available proposition only
abbrev Legend:= ∀ d:ℕ,Label d→ₗ[ℂ]Label d
variable (A:Compass C D)(Z:ℕ→ Legend)(φ:ℕ→ℕ)(V:Legend)(L: Fin n→ Glyph D)(u:Fin n→ E4)
noncomputable abbrev markedG (x:ℕ→ Fin n→ Cover)(i:Fin n):Bond:= ⟨(L i).width, fun j=> Z (φ j) (L i).width (L i).material,V (L i).width (L i).material,fun j=> x (φ j) i,A.r • u i⟩
variable (y:ℕ→ Fin n→ Cover)
noncomputable abbrev poisedP := List.ofFn (markedG A Z φ V L u y)
lemma fit (hg:grace (D:=D) Z φ V)(hv:Tendsto (fun i=>A.qR (C.N (φ i)) ∘ y (φ i)) atTop (𝓝 u))(l:Fin n): Inform C φ (markedG A Z φ V L u y l):=by
       refine ⟨hg _ (L l).raised _,(((tendsto_pi_nhds.mp hv l).const_smul _).congr ?_)⟩
       intro i; exact (congr_arg (fun p:Points n=> p l) ((A.token_τ _ _).symm)) -- digit p
lemma fitP (hg:grace (D:=D) Z φ V)(hv:Tendsto (fun i=>A.qR (C.N (φ i)) ∘ y (φ i)) atTop (𝓝 u)): Worn C φ (poisedP A Z φ V L u y):=by constructor; intro x hx; obtain ⟨l,rfl⟩:= List.mem_ofFn.mp hx; exact fit A Z φ V L u y hg hv _
open Choir Strip
lemma fits (i:ℕ): task P (φ i) (wade (poisedP A Z φ V L u y) i)=(List.ofFn (treeX P (φ i) (Z (φ i)) L (y (φ i)))).prod:=by
       simp only [task,wade, poisedP,List.map_ofFn]; rfl
lemma positionK : Plata.position (Q:=Q) (poisedP A Z φ V L u y)=List.ofFn fun i=> ((A.r • points u) i,Q.focus none _ (V _ (L i).material)):=by simp only[Plata.position, poisedP,List.map_ofFn]; rfl
lemma uniqueP(h: Injective u):Strip.distinct (Plata.position (Q:=Q) (poisedP A Z φ V L u y)):=by
       rw [Strip.spots,positionK,List.map_ofFn,List.nodup_ofFn]; intro i j hh; apply h; exact smul_right_injective E4 A.realH.ne' hh
variable (hA:Known A)
lemma ballot(i:ℕ)(hp:Plot P A i (Z i))(hu:∀ j,L j∈A.Ω)(hZ:∀ j,(L j).material≠0)(hx: A.qR (C.N i) ∘ y i ∈ flats (Fin n) (2*A.e) (A.v/2))(hw:n ≤ A.K) : Spans (C:=C) i (List.ofFn (treeX P i (Z i) L (y i))).prod n (C.S.spacing A.pB) (A.dB ^ n):=by
       obtain ⟨W,x,hV,hp,hf,hT,hv⟩:= hp.segment n L hu hZ hw (y i) hx; let T':= Column.sky C.S (C.R i) A.pB (C.N i) hV (evenW _ _ hp _) W; let Z':= treeX P i (Z i) L (y i)
       refine ⟨T',x,(fun i=>⇑(Z' i)),rfl,footprint C.S _ _ hV,hf,(fun i=>⟨(hv i).1,_,(hv i).2.1⟩),?_,?_⟩ -- let
       · refine (Finset.prod_le_prod (fun i _=>top_nn ..) (fun i _=> (hv i).2.2)).trans ?_; simp
       rw[List.ofFn_eq_map,List.ofFn_eq_map]; exact Eq.symm (coed ..)
open Massive.Bridge (Chamber Spread Cluster readAt)
open Massive.Bridge.Kly (bloom Steady dome)
open OS.Ground (Panes)
-- permit interface to avoid including large arguments in every result proof.
variable (hp:Tendsto φ atTop atTop)
structure Bankroll (P:Calibration C)(φ:ℕ→ℕ)(Q:Choir)(S: Canopy.KForm Q) : Prop where
       flows : Tendsto φ atTop atTop
       path : ∃ β ε,C.Path β ε -- no change ok
       exposed : Q.Harmony P φ
       blank : S 0 0 0=1 -- can simplify
       here {I:Type} [Fintype I] {σ ρ:ℝ} (f:I→List Bond)(z:I→ℂ)(m:ℕ)(g:ℕ→ℕ)(h:∀ i,Strip.distinct (Plata.position (Q:=Q) (f i)))(hS:Tendsto g atTop atTop)(hz:Available P (φ ∘ g) f z ρ σ m)(hp:∀ i,Worn C (φ∘g) (f i))(hU:0 ≤ ρ)(hs:0<σ): ‖∑ i:I,z i * S (Plata.position (Q:=Q) (f i)).length (locus (Plata.position (Q:=Q) (f i))) (fun j=> ((Plata.position (Q:=Q) (f i)).get j).2)‖ ≤ ρ
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.fitP
#print axioms YM.Intag.Sprig.Compass.ballot
#print axioms YM.Intag.Sprig.Compass.Bankroll
