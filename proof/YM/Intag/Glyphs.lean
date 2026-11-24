import YM.Intag.Tess
import YM.Talis.Birth
import YM.Talis.Nectar
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Hymnal
open Pilgrim Tess
open MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV
open UV UV.Free QCD.Grass
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
variable {l c f:Side}(T:Tiling f)(k:T.Cell)
variable {I:Type}[Fintype I](x:I→ Cover)(R:List I)
variable {D:ℕ} (sy:RawSym)(P:I→ Glyph D)
-- integer width horizon.T.Nonempty support.AP memory path metadata.U semantics demands choose future.Yet basis uniqueness in Cam. `Glyphs.image` ≤ fin.Synchronize.
local notation "l'" j:arg=> pathT T (crestT T k j)
noncomputable abbrev reversa (j:T.Cell): List Axis:= ((pathT T (crestT T k j)).map Cells.Cut.pos)
local notation "j'"=> T.Cell× I
local notation "J"=> T.Cell× I
noncomputable def flipX (p: Glyph D) (v:List Axis) : UV.Label p.width:= Massive.Patria.Hub.spine sy p.material v
lemma flared (p:Glyph D)(v:List Axis): (flipX sy p v).val ∈ Rtg p.width p.eng p.gauge p.spin:=by
    induction v with| nil=>exact p.tokens | cons a v ih=> exact Massive.Evo.reflected a sy _ ih
noncomputable def packP (p:Glyph D)(v:List Axis): Glyph D:= ⟨p.width,p.eng,p.gauge,p.spin,flipX sy p v,p.raised,p.hEng,p.hGas,p.hSpin, flared sy p v, Classical.choose (Massive.Evo.boarded _ (flared sy p v)), Classical.choose_spec (Massive.Evo.boarded _ (flared sy p v))⟩
noncomputable abbrev siteP (v:T.Cell×I) : Glyph D:= packP sy (P v.2) (reversa T k v.1)
-- at root source may differ actual P; uses boarded of same Y val.
lemma short (v:T.Cell): (reversa T k v).length ≤8:=by simp only [reversa,pathT,List.length_map]; exact (path T k v).2.trans (routes T k v)
open Finset
private lemma apert (i:ℕ): ∃ s:Finset (List Axis), ∀ j:List Axis,j.length ≤ i→j∈s:=by
    induction i with| zero=>exact ⟨{[]},fun j h=> List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h) ▸ mem_singleton_self _⟩ | succ i ih=> obtain ⟨s,h⟩:=ih; refine ⟨insert [] ((univ:Finset Axis).biUnion fun i=> s.image fun j=> i::j),fun j hj=>?_⟩; cases j with | nil=> simp| cons a j=> exact mem_insert_of_mem (mem_biUnion.mpr ⟨a,mem_univ _, mem_image_of_mem _ (h j (Nat.le_of_succ_le_succ hj))⟩)
noncomputable abbrev jogs (s:Finset (Glyph D)):= s.biUnion (fun i=> (Classical.choose (apert 8)).image (packP sy i))
-- no dependence on clock/lattice arguments. captures glyph of any calibrated era.
lemma reserve (s:Finset (Glyph D))(hp:∀ i:I,P i∈ s)(v:T.Cell× I): siteP T k sy P v∈ jogs sy s:= mem_biUnion.mpr ⟨_, hp _, mem_image_of_mem _ (Classical.choose_spec (apert 8) _ (short ..))⟩
-- uniform stamps.S.Core at v.^ Raw pointer support.
set_option quotPrecheck false
local notation "Rv" i:arg=> post T k i
local notation "Ov" => siteP T k sy P
local notation "Lv" i:arg=>(P i).width
local notation "Sv" i:arg=>(P i).spin
local notation "Fv" i:arg=>shove T k i
local notation "Z!" r:arg=> shows (I:=I) T k r
local notation "L!"=> fun v:J=> (P v.2).width
local notation "S!"=> fun v:J=> polarity (P v.2).spin
local notation "V!"=>fun v:J=> Arise.Bill.port (S!) (L!) v ((siteP T k sy P v).source)
set_option quotPrecheck false -- already issue before?
-- order touring quaternion exact.
lemma polarization (r:T.Cell)(v:T.Cell× I): (S!) ((Z! r) v)=(S!) v:=rfl
lemma writes (r:T.Cell)(h:r≠k): reversa T k r=(post T k r).2:: reversa T k (μ T k r):=by unfold reversa; rw [away_p T k h]; rfl
variable (hx: R.Nodup) (hu:∀ i,i∈ R)
lemma revealed (r:T.Cell)(v:j') (h:r≠k)(ht:v.1=μ T k r) : (siteP T k sy P ((shows T k r) v)).material= sy.adj (P v.2).width (post T k r).2 (siteP T k sy P v).material :=by
     change flipX sy (P v.2) (reversa T k _) =sy.adj (P v.2).width _ (flipX sy (P v.2) (reversa T k _)); rw [show ((Z! r) v).1=r from (by change Equiv.swap (μ T k r) r v.1=r; rw [ht,Equiv.swap_apply_left]),writes T k r h,ht]; rfl
lemma impetus (p:Glyph D): meaning _ _ p.source=p.material.val:=by rw [parcelO, p.core]; exact revive p.material.val ((label_law _).mp p.material.property).1
local notation "G" r:arg=> letter T k R r
local notation "Φ"=> hof T k
variable (hT:T.kind=.link)(w:ℝ)(n:ℕ)
include hx hu
open YM.Bloom.Jar
lemma placards (r:T.Cell)(i:T.Cell× I)(h:r≠k)(ht:i∈ letter T k R (μ T k r)) : meaning (P i.2).width (polarity (P i.2).spin) (siteP T k sy P ((shows T k r) i)).source = UV.adj (post T k r).2 (meaning _ _ (siteP T k sy P i).source):=by
     exact Eq.trans (impetus (siteP T k sy P ((shows T k r) i))) ((congr_arg Subtype.val (revealed T k sy P r i h ((wealthT T k R hx hu _).2 i|>.mp ht))).trans ((sy.adjActs ..).trans (congr_arg _ (impetus (siteP T k sy P i)).symm)))
variable {A: Type}[Fintype A]
local notation "𝔜"=> posT w n ∘ hof T k hT x
local notation "K!"=>fun v:J=> (siteP T k sy P v).source
local notation "Z"=>pays (U:=A) (S!) (L!) 𝔜 (K!)
local notation "Q'"=> S!
lemma obey (r:T.Cell)(h:r≠k)(C:Matrix A A ℂ) (V:Matrix (Spine J) (Spine J) ℂ)(hV:∀ i:J, staysM V (mono (burst (S!) {i}))=grade (mono (burst (S!) {(Z! r) i})))(hp:Set.InjOn (posT w n ∘ hof T k hT x) ((letter T k R (μ T k r)).toFinset:Set (T.Cell × I)))(v:Finset (T.Cell × I))(hz:v⊆(letter T k R (μ T k r)).toFinset): Quills.Eden.antiE (Matrix.fromBlocks C 0 0 V) (Play.Chamber.cetacea (Arise.Count.pence (stampU A (L!) 𝔜) (V!)) v) = Play.Chamber.cetacea (Arise.Count.pence (stampU A (L!) 𝔜) (V!)) (v.map (Z! r)):=by -- cet namespace
     exact MassiveQCD.Sample.Quills.Eden.shores Q' Q' (shows T k r) (fun i=>rfl) C V hV (L!) (K!) (K!) (post T k r).2 𝔜 𝔜 (posT w n (Pilgrim.passport T k hT (u:=r))) _ hp (fun i hi=> neighbors T k x R hT hx hu w n r h i (List.mem_toFinset.mp hi)) (fun i hi=>placards T k R sy P hx hu r i h (List.mem_toFinset.mp hi)) v hz
end Hymnal
end YM.Intag
#print axioms YM.Intag.Hymnal.reserve
#print axioms YM.Intag.Hymnal.revealed
#print axioms YM.Intag.Hymnal.obey
