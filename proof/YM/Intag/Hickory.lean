import YM.Intag.Glyphs
import YM.Intag.Policy
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Hickory
open Pilgrim Tess Hymnal
open MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV
open UV UV.Free QCD.Grass
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
variable {f c l:Side}(T:Tiling f)(p:T.Cell){j F:ℕ}{sy:RawSym}
variable {I:Type}[Fintype I](x:I→ Cover)(V:List I)
variable {D:ℕ}(P:I→ Glyph D)
open YM.Next.Free
variable {K:Clip}(A:Bed)(Q:Train j)
set_option quotPrecheck false
local notation "Jq"=> T.Cell × I
local notation "WP"=> siteP T p sy P
variable (hT:T.kind=.link)
local notation "Kv"=> hof T p hT x
local notation "Xk" i:arg=> (P i.2).width

variable {a b:ℝ}(w η:ℝ)
variable (h:∀ i:T.Cell × I,(milky 0 A c (G:=su) (d':=(P i.2).width)).IsSymm)
-- x stat stencils are Level f with table at c=f always. reflection purity uses TRUE filters.Full
noncomputable abbrev opening (i:T.Cell × I): Insertion f 6:= ((lotus (P i.2).width A c Q (h i) w η (siteP T p sy P i).material.val) f (hof T p hT x i))
local notation "Y'" => staff (fun i:T.Cell × I=> (P i.2).width) Kv w A Q (fun i=> (siteP T p sy P i).material) h 1 η
local notation "X'"=> opening (sy:=sy) T p x P A Q hT w η h -- binder likely parameter order
lemma candor (hc:c=f)(i:T.Cell×I): Rails.Reference.transit hc ((Y') i : Density c 6)=⇑(opening (sy:=sy) T p x P A Q hT w η h i):=by subst f; unfold staff; change ⇑((↑(1:ℝ):ℂ) • (opening (sy:=sy) T p x P A Q hT w η h i))=_; rw[Complex.ofReal_one,one_smul]
-- reflection equality.X rolls anchor via growth.In absolute footprints.B.Coord.In Chol leases.
open MassiveQCD.Sample Massive.Patria
local notation "μ" r:arg=> Pilgrim.μ T p r
local notation "Kz" r:arg=> post T p r
local notation "κ" r:arg=> T.bandCut (post T p r).1 (post T p r).2
variable (ht:Floor A K c a b)(ha:0<a)(ho:Bid.Sworn A c su)(hp:2≤j)
local notation "fθ" v:arg=> shows (I:=I) T p v
include ht ha ho hp
lemma earns (r:T.Cell)(hr:r≠p) (i:T.Cell×I) (hy:i.1=Pilgrim.μ T p r): tallH (κ r) ⇑(opening (sy:=sy) T p x P A Q hT w η h i)=⇑(opening (sy:=sy) T p x P A Q hT w η h ((fθ r) i)):=by
      let z:= Pilgrim.passport T p hT (u:=r); let C' :=κ r
      let Xv:= (X') i; let k:=(P i.2).width; let Wv:= (siteP T p sy P i).material; let t:=(post T p r).2; let v:= (Kv) i
      let U:=(hof T p hT x) ((fθ r) i)
      have hz: U=C'.flip.act v+z:=by
           unfold U hof; change bout T p hT (x i.2) _=_; rw [show ((fθ r) i).1=r from (by change Equiv.swap _ _ i.1=r; rw [hy,Equiv.swap_apply_left]),bout,dif_neg hr]; apply congr_arg (·+_); apply congr_arg; change _= bout T p hT (x i.2) i.1; rw [hy]
      have hQ : tallH C' Xv = march z ⇑((lotus k A c Q (h i) w η (UV.adj t Wv.val)) f ((Signed.mirror t).act v)):=by
            rw [Massive.Lyre.paintC C' z (paced T p hT r)]; apply congr_arg; exact YM.Eden.spaces v η w t Wv.val A Q (h i) ht ha ho hp -- hp explicit
      let y':= ((fθ r) i)
      let w1:UV.Label k:= (siteP T p sy P y').material; let wx:UV.Label k:= Wv; have hv:w1.val= UV.adj t wx.val:=Eq.trans (congr_arg Subtype.val (Hymnal.revealed T p sy P _ _ hr hy)) (sy.adjActs ..)
      rw [hQ]; change march _ ⇑(lotus k A c Q (h i) w η (UV.adj t wx.val) f _) = ⇑(lotus k A c Q (h i) w η w1.val f U); rw [hz,←hv]; exact YM.Eden.eo .. -- arity
omit ht ha ho hp
end Hickory
end YM.Intag
#print axioms YM.Intag.Hickory.candor
#print axioms YM.Intag.Hickory.earns
