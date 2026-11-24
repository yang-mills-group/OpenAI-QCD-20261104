import YM.Alum.Fables
import YM.Alum.Fables
import YM.Alum.Dews
import YM.Alum.Chord
import YM.Pods.Hoops
import YM.Topaz.Room
import YM.Alum.Greet
import YM.Intag.Shift
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
open QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
-- presentations.From Calibration arrays.SYM
open Massive.Poised Massive.Poised.Plans Stamp Massive.Patria
open QCD.Acre.Stratum.MarchQ.Suburb.MintV
variable {Vb:YM.Source.Hol su}(P: Lining.Temper.Collage.Exhibit Vb) (Θ: Massive.SourceRead.TaperHol)(sy:RawSym)(Y: Massive.Sequence)(U:Lining.Temper.Collage.Exhibit.CoreMix)
variable (R0:Vista (S.side R i) D)(N₀:ℕ) (L:Side)(Ω:Finset (Glyph D))(Hp:Dial D)(z:ℝ)(Dk Uq j₀ ℓ K:ℕ)(ε v εr Xv:ℝ)(hB:ℕ→BudgetPoint)(pv:ℕ→ℝ)(base:ℕ→ℕ)(Qv:∀ d,PatchMix d)(hp:Even R.val)(hk:i≤ N)
variable (hR:Vista.RoofV A R0 hk hp sy Ω Uq K ε v Xv Hp L z j₀ ℓ Θ P εr Dk hB pv base Qv)
open YM.Intag.CardsT
variable (b:Cover)(a:Averaging)(X:Glyph D) (G:UV.Label X.width)
local notation "Zn"=>S.side R
local notation "Zp"=>S.side R p
local notation "Vp"=>viewW S R
local notation "Fo"=>Qv X.width a G
local notation "T!"=>tokenP X R0
-- actual presentation & checked plants.
noncomputable abbrev hXcheckT (ℓ:ℕ)(a:Averaging)(X:Glyph D)(b:Cover):Stud (S.side R N) 6:=Averaging.filter a (ratioTo S i ℓ) (leaf A R0 X) (ratioTo S i ℓ • b)
-- Signature reorder. use.Check.
noncomputable def bornC {Vb:YM.Source.Hol su}(Uv:Lining.Temper.Collage.Exhibit Vb) (X:Glyph D)(T:Vista (S.side R i) D)(u:UV.Label X.width)(b:Cover): Insertion (S.side R N) 6:= (tokenP X T:ℂ) • Bloom Uv X.width (S.side R N) b u -- A not included
noncomputable def hYcheck (b:Cover):Insertion (S.side R N) 6:= Averaging.filter a (ratioTo S N ℓ) (bornC (N:=N) P X R0 (Qv X.width a G)) (ratioTo S N ℓ • b)
local notation "Πt"=> Qv X.width
variable (wK:ℕ)(hr:wK<Hp.e)
local notation "vB"=> Dial.viewAt L Hp z j₀ wK
local notation "Go"=>Dial.rateB L wK z
local notation "q" => polarity X.spin
variable (ht:p=Dial.viewAt L Hp z j₀ wK)(hw:p ≤ ℓ) (x:Site (S.side R ℓ))(y:Site (S.side R p))(hx:X∈Ω) (hm: moored (Qv X.width a G).val (polarity X.spin)) (hy:ℓ≤ i)
local notation "g" =>viewW S R hw
local notation "H₀"=>evenW S R hp p
local notation "Γ"=>mural (viewW S R hw) H₀ x
local notation "T"=> Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x
-- Type B outputs for ANY slot. σ includes U margin. hom despite copying. pay offsets.
include hr hR ht hw hx
lemma oneSlot (m:ℕ)(hZ: wrap _ b∈ (mural g H₀ x).margin y (marginM S Uq p ℓ+102+m))(hs:0<Uq)(u:Cover)(hv:u∈ box (CardsT.flex S ℓ i)): let F:=Vista.leaf A R0 X (ratioTo S i ℓ • b+u); Fence ((Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x).chamber y) F ∧ (∀ Y,Hom q (F Y))∧ topH (Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x) A.regulator F y ≤ Go:=by
     intro F; let C:= pillar S R x i; let H:=hw.trans hy
     have h1: ℓ ≤ N:=hy.trans hk
     have h:= factorL hw hy hp x hk; obtain ⟨hS,hP,hV⟩:= singleB A R0 H hk hp sy C y Ω Dk _ Uq K (Dial.repay L z p) (2*Hp.H) (measureV L Hp.ν z) ε v Xv (Dial.gainB L wK z) (Dial.rateB L wK z) (ht.symm ▸ hR.oneA wK hr) X (ratioTo S i ℓ • b+u) hx (padding _ _ _ _ _ (viewOdd S R (hw.trans hy)) (budding hw hy hp x y Uq hs b m u hv hZ) (by omega))
     have hT: Column.pillar S R (Column.pillar S R x i) N= Column.pillar S R x N:=by unfold Column.pillar; rw [dif_pos hy,dif_pos hk,dif_pos h1]; rw [embed_comp (viewW S R hy) (viewW S R hk)]
     unfold C at hS hV; unfold Column.sky; rw[← hT]; exact ⟨hS, polLeaf A R0 (fun _:Unit=>X) (fun _=> ratioTo S i ℓ • b+u) hk (),hV⟩
-- credit averaging X price.B
variable (hsm:Goblet.Smoke (Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x) A.regulator)
lemma oneX (m:ℕ)(hZ: wrap _ b∈ (mural g H₀ x).margin y (marginM S Uq p ℓ+102+m))(hs:0<Uq) (hb:Goblet.Smoke (Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x) A.regulator): Fence ((Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x).chamber y) (hXcheckT A R0 ℓ a X b) ∧ (∀ Y,Hom q ((hXcheckT A R0 ℓ a X b) Y))∧ topH (T) A.regulator (hXcheckT A R0 ℓ a X b) y ≤ Go:=by
      let Y':= leaf A R0 X; obtain ⟨f,hf,hfv,hk'⟩:= strummed S b a Y' hy; let E:=↥(box (CardsT.flex S ℓ i)); let t(i':E):= Y' (ratioTo S i ℓ • b + i'.val); have h(i':E):=oneSlot A P Θ sy R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR b X wK hr ht hw x y hx hy m hZ hs i'.1 i'.2 -- arg
      unfold hXcheckT; rw [show Averaging.filter _ _ _ _=∑ i':E,f i' •t i' from hk']; refine ⟨shelter _ _ _ (fun i hi=> (h i).1.mass (↑(f i):ℂ)),?_,?_⟩; · intro i; rw [Finset.sum_apply]; exact Grass.Hom.sum (fun j _=> ((h j).2.1 i).smul _)
      exact sturdyR (T) A.regulator y (Go) f t hf hfv q (fun i=>(h i).1) (fun i=>(h i).2.1) hb (fun i=>(h i).2.2)
omit hr hR ht hw hx
-- fix Args. base! Temple.
include hm hw
lemma oneY (m:ℕ)(hZ: wrap _ b∈ (mural g H₀ x).margin y (marginM S Uq p ℓ+102+m))(hs:0<Uq)(hv:kingT ((P.display Y Θ sy U base).stencil X.width) ≤ ratioTo S N ℓ * m): Fence ((Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x).chamber y) (hYcheck P R0 ℓ Qv a X G b) ∧(∀ V, Hom q ((hYcheck (N:=N) P R0 ℓ Qv a X G b) V)):=by
      let Lx:= bornC (N:=N) P X R0 (Fo); obtain ⟨f,he,hv',hz⟩:=strummed S b a Lx (hy.trans hk); let I:=↥(box (CardsT.flex S ℓ N)); let Xb(j:I):=ratioTo S N ℓ • b+j.val; let Hy(j:I):=Lx (Xb j)
      have h(v:I):= kingFlow P Θ sy Y U base (Xb v) (T) y _ _ (polarity X.spin) hm (budding hw (hy.trans hk) hp x y Uq hs b m v.val v.property hZ) (hv.trans (Nat.le_add_left _ _)) rfl
      unfold hYcheck; rw[show Averaging.filter _ _ _ _ = ∑ i:I,f i• Hy i from hz]; constructor
      · rw [ContinuousMap.coe_sum]; exact shelter _ _ _ (fun i hh=> ((h i).2.1.mass _ |>.mass (↑(f i):ℂ)))
      intro V; rw [ContinuousMap.sum_apply]; exact Grass.Hom.sum fun i hh=> ((h i).2.2 V).smul _|>.smul (↑(f i):ℂ)
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.oneX
#print axioms YM.Intag.Tarot.Vista.oneY
#print axioms YM.Intag.Tarot.Vista.hYcheck
