import YM.HONE.Infl
import YM.Intag.Mint
import YM.Intag.Hickory
import YM.TIPS.Reg
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

-- for EP and distinct Tile pitches, probes remain same via glyph.B.c Not attaching erasures from V.Full.Photo. Use.
variable (U:Glyph D)(O:BudgetPoint) (Hv: (milky 0 A c (G:=su) (d':=U.width)).IsSymm) (q:ℝ)
noncomputable abbrev realm (i:T.Cell): Glyph D:= packP sy U (reversa T p i)
local notation "Ht" i:arg=>reversa T p i
local notation "Zt"=>realm (sy:=sy) T p U
noncomputable abbrev toga (i:T.Cell): Cover→ Insertion c 6:= ((Zodiac U.width U.eng U.gauge U.spin w η O.threshold q A c Q Hv ((realm (sy:=sy) T p U i).material)) c) -- not reducible Label? inspect.
local notation "Φ"=>toga (sy:=sy) T p A Q w η U O Hv q
lemma steep (i:T.Cell)(h0:U.material≠0): (Zt i).material≠ 0:=by
      have hi (v:List Axis):(packP sy U v).material ≠0:=by
           change flipX sy U v≠0; induction v with| nil=> exact h0|cons a v ih=> change sy.adj _ _ _≠0; rw [LinearEquiv.map_ne_zero_iff]; exact ih
      exact hi _
lemma earnsE (R:Finset (Glyph D))(h:U∈ R)(i:T.Cell): Zt i ∈ Hymnal.jogs sy R:= Hymnal.reserve T p sy (fun _ :Unit=>U) R (fun _=>h) (i,())
lemma P0 : (Zt p).material= U.material:=by change flipX sy U _= _; unfold reversa; rw[Pilgrim.at_p]; rfl
noncomputable abbrev seedY := (Zodiac U.width U.eng U.gauge U.spin w η O.threshold q A c Q Hv U.material) c
lemma gardenR: Φ p = seedY A Q w η U O Hv q :=by unfold toga seedY; rw[P0] -- order P0 explicit
local notation "Ψz"=>Ten U.eng U.gauge U.spin w η O.threshold q
variable (hA:Floor A K c a b)(hC:0 < a)(hj:2 ≤ j)(ho:Bid.Sworn A c su)
include hj
lemma claims (i:T.Cell)(x:Cover)(V:Grid c):Grass.Hom (polarity U.spin) (Φ i x V):=Massive.Evo.polarE _ (Zt i|>.tokens) w η Q hj x V -- sig.
open Cylinder Massive.Patria
lemma markedU (i:T.Cell)(a b:Cover): Massive.Patria.march b ⇑(Φ i a)= ⇑(Φ i (a+b)):=by
     let Qe:= (Zt i).material; let W:= lotus U.width A c Q Hv w η Qe.val; let t:ℂ:= Ψz
     change march b (t⁻¹ • ((W c a): Density _ 6)) =t⁻¹ • ⇑(W c (a+b)); have ht:march b ⇑(W c a)=⇑(W c (a+b)):=YM.Eden.eo ..
     funext X; exact (map_smul (TorusPCAC.Geometry.crank 1 1 (wrap _ b) (TorusPCAC.Geometry.heat b)) t⁻¹ _).trans (congr_arg (t⁻¹ •·) (congr_fun ht X)) -- check namespace
include hA hC ho
lemma adjT (i:T.Cell)(g:i ≠ p)(b:Cover): Massive.Cylinder.Action.adj (Pilgrim.post T p i).2 ⇑(Φ (Pilgrim.μ T p i) b)= ⇑(Φ i ((Signed.mirror (Pilgrim.post T p i).2).act b)):=by
      let r:=Pilgrim.μ T p i; let a:=(post T p i).2; have ht: ((Zt i).material: Label U.width)=sy.adj _ a ((Zt r).material):=by suffices h: flipX sy U (Ht i)=sy.adj _ (post T p i).2 (flipX sy U (Ht r)) from h; rw [writes T p i g]; rfl -- writes args
      let K:= Zt r; let W (p: Pol U.width):=lotus U.width A c Q Hv w η p
      let v:=(Signed.mirror a).act b; let M:= W (K.material.val) c b; let N:= W ((Zt i).material.val) c v
      have he:Action.adj a ⇑M= ⇑N:=by
            suffices hh: ((Zt i).material.val : Pol U.width) = UV.adj a K.material.val by unfold N; rw [hh]; exact YM.Eden.spaces b η w a _ A Q Hv hA hC ho hj -- field binders
            exact (congr_arg Subtype.val ht).trans (sy.adjActs ..)
      let q:= (Ψz:ℝ); change Action.adj a ((q:ℂ)⁻¹ • (M : Density _ 6))=(q:ℂ)⁻¹ • ⇑N; rw[←he]; funext x; rw [Exposure.eye_value,Pi.smul_apply,map_smulₛₗ, map_inv₀,show (starRingEnd ℂ) (q:ℂ)= _ from Complex.conj_ofReal q]; simp only [Pi.smul_apply, Exposure.eye_value]
end Hickory
end YM.Intag
#print axioms YM.Intag.Hickory.adjT
#print axioms YM.Intag.Hickory.claims
#print axioms YM.Intag.Hickory.earnsE
#print axioms YM.Intag.Hickory.markedU
#print axioms YM.Intag.Hickory.gardenR
#print axioms YM.Intag.Hickory.steep
