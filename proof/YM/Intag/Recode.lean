import YM.Intag.Reclaim
import YM.Intag.Yell
/-! # literal reading on the ACTUAL stencils. Root letters memory.L.Piece--sector-ready.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Tarot
open Pilgrim Tess Hymnal MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV UV UV.Free QCD.Grass QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon Quills.Clover
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
open Column Massive.Evo
variable {S:Scheme}{R:Side}{i j k p N:ℕ}(A: Massive.Run S N R 6) {f l:Side}{D:ℕ}
namespace Vista
open YM.Bloom.Jar YM.Bank YM.Bank.Jule
variable {I: Type}[Fintype I] (B:Vista (S.side R i) D)(P:I→ Glyph D)(x:I→ Cover)
set_option quotPrecheck false
local notation "Tz"=> fun i:I=>polarity (P i).spin
local notation "Tk"=> fun i:I=>(P i).width
variable (he:i ≤ N)(hv:p ≤ i)(w:Site (S.side R i))(ho:Even R.val) (sy:RawSym) (v:Site (S.side R p))(L: List I) (d:ℕ)(Z:ℝ)
local notation "hp"=> evenW S R ho p
local notation "G"=> viewW S R hv
set_option quotPrecheck false
local notation "T"=>mural (viewW S R hv) hp w
noncomputable abbrev ProbeWords (Y:I→ E4)(X:I→ Stud f 6)(hX:∀ i H,Hom (polarity (P i).spin) (X i H)) := fun H=> wordA (A:=Keys f 6) Tz Y Tk (fun i=> X i H) (fun i=> hX i H) (fun i=> (P i).source) L -- h property data
include he in
lemma polLeaf(i':I)(H:Grid (S.side R N)) : Hom (polarity (P i').spin) (leaf (i:=i) A B (P i') (x i') H):=by
      have ht:= Lyre.steep A (⇑(specimen B P x i')) (polarity (P i').spin) (stands (i:=i) B P x _) (power (i:=i) B P x _) he H
      unfold specimen staff at ht; simp only [Pi.one_apply,Complex.ofReal_one,one_smul] at ht; exact ht
-- high hΩ.ACC for all. local equality.Momentum.
local notation "PP"=> asset hv ho sy w v P
local notation "xx"=> placeQ hv ho w v x
local notation "Rv"=> Tess.letter (mural G hp w) v L
local notation "st"=> (S.side R p)
local notation "Jq"=> Site (S.side R p)× I
variable (S₁: Finset (Site (S.side R p)× I)→ Patio (Spine (Site (S.side R p)× I)))
variable (hA: QuillCore (asset hv ho sy w v P) (placeQ hv ho w v x) S₁ true (Folio.ink (show Site (S.side R p) × I→Site (S.side R p) from Prod.fst)) d Z)
-- Pub proof hD not transported. grade Σ births.
local notation "C"=>Finset -- remove
variable (hL:L.Nodup)(hF:∀ i:I,i∈L)
noncomputable def aboard : I↪ Site (S.side R p) × I:=⟨Prod.mk v,fun i j h=> congr_arg Prod.snd h⟩
local notation "Kv"=> aboard v (I:=I)
lemma aboard_spec (j:I) : placeQ hv ho w v x ((aboard v) j)=x j:= Tess.spec (mural G hp w) v rfl _ rfl -- syntax hT
lemma label_aboard (j:I): (asset hv ho sy w v P ((aboard v) j)).material=(P j).material:=by change flipX sy (P j) _ =_; change flipX _ _ (Hymnal.reversa (mural G hp w) v v)= _; rw [reversa,Pilgrim.at_p (mural G hp w) v]; rfl
lemma aboard_list : Tess.letter (mural G hp w) v L v=(L.map (aboard v)):= Tess.at_p _ _ L
include hA hL hF
open Play Play.Chamber
lemma rootE (hw: Injective (posT Z d∘x)): Vista.effort A B he (asset hv ho sy w v P) (placeQ hv ho w v x) S₁ (Tess.letter (mural G hp w) v L v) = fun H => ProbeWords P L ((posT Z d) ∘ x) (fun i':I=>Vista.leaf (i:=i) A B (P i') (x i')) (polLeaf A B P x he) H:=by -- probe arity
      funext V; let C':= Keys (S.side R N) 6; let u:= aboard v (I:=I)
      let Y'(i':Jq):= climbH A i N (specimen (i:=i) B (asset hv ho sy w v P) (placeQ hv ho w v x) i') V
      let X' i:= Vista.leaf A B (P i) (x i) V; let d'(j:Jq):= ((asset hv ho sy w v P) j).width
      have hpQ (i':I): Hom ((Tz) i') (X' i'):= polLeaf A B P x he _ _
      let Q':=fun j:Jq=>polarity ((asset hv ho sy w v P) j).spin
      have hpP (j:Jq): Hom (Q' j) (Y' j):= Lyre.steep A _ _ (stands B PP xx j) (power B PP xx j) he _
      have hm(i:I): (Tz) i=Q' (u i):=rfl
      have hT(j:I): meaning (d' (u j)) (Q' (u j)) ((asset hv ho sy w v P) (u j)).source= meaning _ _ (P j).source:=((impetus ..).trans (congr_arg Subtype.val (label_aboard P hv w ho sy v j))).trans (impetus ..).symm -- args inspect label
      have hZ(i:I): (posT Z d ∘ xx) (u i)=(posT Z d ∘ x) i:=congr_arg _ (aboard_spec ..) -- fixes
      have hY(i:I): Y' (u i)=X' i:= congr_fun (Vista.born A B hv ho sy w v P x i) V
      let Ω:= L.toFinset
      let W:=L.map u; let Λ : Jq→ E4:= YM.Bloom.Jar.posT Z d ∘ xx; let Qc (j:Jq): Cups (d' j) (Q' j):= ((asset hv ho sy w v P) j).source
      have hR:=figure (A:=C') Tz Q' u (fun i=> (hm i).symm) d' (fun i=> (P i).source) Qc (posT Z d∘ x) Λ Ω hw.injOn (fun i _=>hZ i) (fun i _=>hT i) X' Y' hpQ hpP L rfl (fun i _=>hY i) hL -- arity check
      have hC:(Rv) v=W:= aboard_list hv w ho v L
      change Vista.effort A B he _ _ S₁ ((Rv) v) _ = wordA Tz _ Tk _ _ (fun i=>(P i).source) L
      apply Eq.trans _ hR
      rw [hC]; let Wp(i:Jq):=emitK Q' i (Y' i) (hpP i)
      -- use finset discrepancy erase κ.M.Can.P.F.B rule.
      -- toFinset inside kits classical; outside `[DecidableEq (Site×I)]` differs; express lemma universal
      have hE (s': Finset Jq)(ht0:s'.Nonempty)(hh:∀ i∈s',i ∈ W): qraft C' _ (S₁ s')= -cetacea (Arise.Bill.pays (U:=C') Q' d' Λ Qc) s':=by
           have hv:= hA.chit; rw [if_pos rfl] at hv; let P':=Folio.ink (show Jq→Site (S.side R p) from Prod.fst); have he(j:Jq)(hj:j∈s'):j.1=v:=by obtain ⟨i,_,rfl⟩:=List.mem_map.mp (hh j hj); rfl
           exact hv _ ((Folio.ort ..).2 (fun i hi j hj=> (he i hi).trans (he j hj).symm)) ht0 _
      unfold wordA; change chants Q' W C' _ =chants Q' W C' _; apply congr_arg; change kits _ Wp _ = kits _ Wp _; unfold kits; -- sums may Finset coercivity.He.
      congr 2; refine sum_congr rfl fun i hi=> ?_; letI:DecidableEq (Site (S.side R p) × I):=fun x y=> Classical.propDecidable _; exact hE _ (nonempty_iff_ne_empty.mpr (ne_of_mem_erase hi)) (fun x hx=>List.mem_toFinset.mp (mem_powerset.mp (mem_of_mem_erase hi) hx))
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.rootE
