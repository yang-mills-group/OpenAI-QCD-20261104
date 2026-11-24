import YM.Intag.Sparks
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Tarot
open Pilgrim Tess Hymnal
open MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV
open UV UV.Free QCD.Grass
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
open Column Massive.Evo
variable {S:Scheme}{R:Side}{i j k p N:ℕ}(A:Massive.Run S N R 6)
variable {f:Side}{D:ℕ}
namespace Vista
open YM.Bloom.Jar YM.Bank YM.Bank.Jule
variable {I:Type}[Fintype I](P:I→ Glyph D)(x:I→ Cover) (f0:I→Site f)(c:Site f→ List I)
local notation "T"=> Folio.ink f0
variable (h:Folio.Muster f0 c)
-- hΘ generation consent.Body. choose across all alph.Ar. 
variable (d:ℕ)(W:ℝ)
set_option quotPrecheck false
local notation "q"=> fun j:I=> polarity (P j).spin
local notation "L"=> fun j:I=> (P j).width
local notation "v"=> fun j:I=> (P j).source
local notation "Φ"=> fun j:I=>Arise.Bill.port q L j ((v) j)
include h
lemma miracle (hv:∀ i,Set.InjOn (posT W d∘ x) ((c i).toFinset:Set I)):∃ S₁, QuillCore P x S₁ true T d W:=by
    obtain ⟨S₁,hS⟩:= Massive.Lyre.provenance q L v (posT W d∘ x) (univ:Finset (Site f)).toList c (fun i _=>hv i); rw [← Folio.prepay f0 _ h] at hS; exact ⟨S₁,fun i hi hh=> (hS i (mem_erase.mpr ⟨hh.ne_empty,hi⟩)).1,by
       rw [if_pos rfl]; intro i hi hh A _; exact (hS i (mem_erase.mpr ⟨hh.ne_empty,hi⟩)).2 A⟩
omit h
lemma nilQuill (K: Finset (Finset I)): QuillCore P x (fun _=>0) false K d W:=by
    refine ⟨fun i _ _=>fun A _=>?_, by simp; rfl⟩
    rw [map_zero]; refine ⟨0,?_⟩; rw[map_zero]; rfl
-- Unity single true value for any singleton. 
lemma solo (B:Vista (S.side R i) D) (he:i≤ N)(p:I): Vista.effort A B he P x 0 [p]= climbH A i N ((specimen B P x p):Density (S.side R i) 6):=by
      let V: I→Stud (S.side R N) 6:=fun j=>climbH A i N ((specimen B P x j):Density _ _)
      let w:=fun j:I=> polarity (P j).spin; funext U; let X' j:=V j U
      have hh(j:I): Grass.Hom (w j) (X' j):= Lyre.steep A _ _ (stands B P x j) (power B P x j) he U
      let L':List I:=[p]; let u:= L'.get; let F:=L'.toFinset; let C:=Keys (S.side R N) 6; let Y(j):=emitK w j (V j U) (hh j)
      unfold effort tokenV; -- target about radiant constants qraft Ω.Prop
      simp only [kits,comp_apply,Pi.zero_apply,map_zero, Finset.sum_const_zero,NormedSpace.exp_zero,mul_one]
      have ht : Injective u:= List.nodup_iff_injective_get.mp (List.nodup_singleton _)
      change chants w _ C _ = X' p; refine Eq.trans (Massive.Lyre.regalL w (G:=C) u X' hh F (by rw[show Quills.crest u=F from tops L']) ht) (?_); -- list equality
      change (List.ofFn (X' ∘ u)).prod=X' p; rw [←List.map_ofFn]; simp [u,L']
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.nilQuill
#print axioms YM.Intag.Tarot.Vista.solo
#print axioms YM.Intag.Tarot.Vista.miracle
