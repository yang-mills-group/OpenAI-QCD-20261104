import YM.Intag.Mint
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
variable (B:Vista (S.side R i) D) (hv:p≤ i) (he:i ≤ N)
namespace Vista
open YM.Bloom.Jar YM.Bank YM.Bank.Jule
variable (ho:Even R.val)(sy:RawSym)
local notation "F"=> S.side R
local notation "hp"=> evenW S R ho p
local notation "Hq"=> viewW S R hv
variable (z:Site (S.side R i))(x0:Site (S.side R p))
-- sector.A cost for actual generation N.C.Center p coarse.
local notation "T"=>mural (viewW S R hv) hp z
variable {I:Type}[Fintype I](P:I→ Glyph D)(x:I→ Cover)(l: List I)
local notation "Jq"=>Site (S.side R p) × I
set_option quotPrecheck false
local notation "W"=> siteP (mural Hq hp z) x0 sy P
noncomputable abbrev asset : Site (S.side R p) × I→ Glyph D:= siteP (mural Hq hp z) x0 sy P
noncomputable abbrev placeQ : Site (S.side R p) × I→ Cover := hof (mural (viewW S R hv) (evenW S R ho p) z) x0 rfl x
-- use these with Owner.Time.En. constructors hit all.Support.Calendar.V. Need separate numbers hP.H.Kind.Shape.G.
structure Reception (X Mq X' :ℕ)(t q b:ℕ)(TQ:ℝ)(ε v:ℝ) :Prop where
     unit: l.Nodup ∧∀ u,u∈ l
     cards:Fintype.card I≤t
     costs : 0<ε
     lines : ∀ u,wrap (S.side R i) (x u)∈(mural (viewW S R hv) (evenW S R ho p) z).margin x0 X'
     pulse : X ≤ X'
     /-- tighter arcs use λ.P rejection. Mq phantom? remove -/
     figure : ratioTo S i q * (Mq*Mq+1) ≤2*X' -- q repack, Mq radiusPt
     wounds : ∀ a v:I,separation (wrap (S.side R i) (x a)) (wrap (S.side R i) (x v)) ≤ ratioTo S i q
     hefty u v : u≠v→ 2*X < separation (wrap (S.side R i) (x u)) (wrap (S.side R i) (x v))
     stamps : ∀ t i:I,t ≠ i → YM.Bloom.Jar.posT TQ b (x t) - YM.Bloom.Jar.posT TQ b (x i) ∈ Oasis ε v
-- raffle producer.Shape only XP. no B ancillary.
variable (X Mq X' t j0 b0:ℕ)(r:ℝ)(ε Y:ℝ)
variable (h: Reception (p:=p) hv ho z x0 x l X Mq X' t j0 b0 r ε Y)
local notation "a0"=>asset hv ho sy z x0 P
local notation "O"=>placeQ hv ho z x0 x
local notation "Rv"=> Tess.letter (mural Hq hp z) x0 l
local notation "f!"=>show Jq→Site (S.side R p) from Prod.fst
local notation "V"=> Folio.ink (f!)
local notation "K!"=> Vista.effort A B he a0 O
variable (Pset:Finset (Glyph D))(Xv qv:ℝ)(Mode:Bool)
variable (hz: Credential A B he (Hymnal.jogs sy Pset) X p t Mq b0 j0 r ε Y Xv qv Mode)
variable (hw: ∀ t:I,P t∈ Pset)
include h hw hz
-- conditioning posterior prototype reuse survivors of projected tiles.Anchor.Comb. theorem uses t not P. launches ALL glyphs.
local notation "E"=>S.side R i
local notation "c!"=>S.side R p
variable (hc:B.r +1+50*(S.J i+10) ≤ X)
include hc
omit h hw hz hc in
private lemma licenses {I:Type}[Fintype I](f: Side)(k:ℕ)(hk:Fintype.card I≤ k):Cupola.Fires (show Site f × I → Site f from Prod.fst) k:=by
     intro u; apply le_trans _ hk;  apply le_trans _ (card_univ (α:=I)).le; exact Finset.card_le_card_of_injOn Prod.snd (fun i _=>mem_univ _) (fun x hx y hy he=> Prod.ext (((mem_filter.mp hx).2).trans ((mem_filter.mp hy).2).symm) he)
lemma ace_l : Posterior a0 (f!) (placeQ hv ho z x0 x) (Tess.letter (mural Hq hp z) x0 l) X B t Mq b0 r ε Y j0:=by
    let v : Jq → Site (S.side R i):= wrap _ ∘ O; have hx(w:Jq):v w∈ (mural Hq hp z).margin w.1 X':= Tess.prices_f (mural Hq hp z) x0 x rfl w.1 w.2 _ (h.lines w.2)
    refine ⟨Tess.muster (mural Hq hp z) x0 l h.unit.1 h.unit.2,fun i=> hz.funds _ (Hymnal.reserve (mural Hq hp z) x0 _ _ _ hw i),hc,?_,⟨hv,ho,z,X',h.pulse,hx,h.figure⟩,?_,licenses _ _ h.cards,Tess.palm (mural Hq hp z) x0 _ rfl r b0 h.costs h.stamps⟩ -- Works arity
    · rintro ⟨a,u⟩ ⟨b,w⟩ he; by_cases hv':a=b; subst a; change _ < separation (((wrap _ ) ∘ hof _ _ _ x) _) (((wrap _ ) ∘ hof _ _ _ x) _); exact lt_of_lt_of_eq (h.hefty u w (fun h=>he (Prod.ext rfl h))) (cups_f (mural Hq hp z) x0 x rfl b u w).symm
      apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left h.pulse (Nat.zero_le 2)); rw [two_mul]; exact crimp Hq z a hp (viewOdd ..) (hx (a,u)) (hx (b,w)) hv'
    rintro ⟨a,u⟩ ⟨b,v⟩ (he:a=b); subst a; exact Eq.trans_le (cups_f (mural Hq hp z) x0 x rfl b _ _) (h.wounds u v)
-- hQ witness chosen or input. output Base replica.Top.Port. `tightA` etc reader uniform.SE implement next.
omit hz hc hw
lemma stocks : ∀ j:Site (S.side R p), Set.InjOn (YM.Bloom.Jar.posT r b0 ∘ hof (mural Hq hp z) x0 (show _ from rfl) x) ((Tess.letter (mural Hq hp z) x0 l j).toFinset:Set ((mural Hq hp z).Cell× I)):=by
     intro j i hi k hk hh; let v : List Jq:= Rv j; have hm:Folio.Muster (f!) (Tess.letter (mural Hq hp z) x0 l):= Tess.muster (mural Hq hp z) x0 _ h.unit.1 h.unit.2; have hx : v.toFinset∈ Folio.ink (f!):=(Folio.ort ..).mpr (fun i hi k hk=> ((hm.address j i).mp (List.mem_toFinset.mp hi)).trans ((hm.address j k).mp (List.mem_toFinset.mp hk)).symm)
     have hP: PalmT ((YM.Bloom.Jar.posT r b0) ∘ placeQ hv ho z x0 x) v.toFinset ε Y:= Tess.palm (mural Hq hp z) x0 _ rfl r b0 h.costs h.stamps _ hx -- mismatch Dec
     exact Classical.byContradiction fun hv=> sub_ne_zero.mp (door (hP.test _ hi _ hk hv) h.costs) hh
-- `Pset` before positive. no reliance on membership in Era.B_H.
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.ace_l
#print axioms YM.Intag.Tarot.Vista.stocks
