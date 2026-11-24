import YM.Alum.Briars
import YM.Alum.Briars
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
-- Signature reorder. use.Check.
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
include hr hR hw hy ht hx
variable (hx':X.material≠0)(hw': Tally Θ 0 G (A.density (base X.width)) (CardsT.tentT A a (spire X R0) (base X.width) 0))
local notation "Wp" => Dial.worthA L Hp z
local notation "χ"=> hXcheckT A R0 ℓ a X b
local notation "η"=> hYcheck (N:=N) P R0 ℓ Qv a X G b
include hx' hw'
set_option maxHeartbeats 430000
lemma activeQ (m:ℕ)(hZ: wrap _ b∈ (mural g H₀ x).margin y (marginM S Uq p ℓ+102+m))(hs:0<Uq)(hv:kingT ((P.display Y Θ sy U base).stencil X.width) ≤ ratioTo S N ℓ * m)(hb:Goblet.Smoke (Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x) A.regulator) : Fence ((Column.sky S R p N (hw.trans (hy.trans hk)) H₀ x).chamber y) (hYcheck (N:=N) P R0 ℓ Qv a X G b) ∧(∀ V, Hom q (η V))∧ Fence ((T).chamber y) (hXcheckT A R0 ℓ a X b) ∧ (∀ V,Hom q ((hXcheckT A R0 ℓ a X b) V))∧ topH (T) A.regulator (hXcheckT A R0 ℓ a X b) y ≤ Go ∧topH (T) A.regulator (η) y ≤ Go+Wp ∧topH (T) A.regulator (⇑(η)- (hXcheckT A R0 ℓ a X b)) y ≤ Wp ∧ moored (Qv X.width a G).val q:=by -- coe add use ⇑
     subst p
     obtain ⟨yK,hτ,hM,_,h⟩:=(hR.bloom X hx hx' a wK hr x (hy.trans hk) hw b y).votes (padding _ _ _ _ _ (viewOdd S R hw) hZ (by omega))
     rw [Canvas.consensus Θ 0 _ hτ G hw'] at h hM
     have hu:Fence ((Column.sky S R (Dial.viewAt L Hp z j₀ wK) N (hw.trans (hy.trans hk)) (evenW S R hp _) x).chamber y) (hYcheck (N:=N) P R0 ℓ Qv a X G b) ∧ ∀ V,Hom q (η V):=oneY P Θ sy Y U R0 Uq ℓ base Qv hp hk b a X G hw x y hM hy m hZ hs hv -- arg
     obtain ⟨hV,hQ,hA'⟩:=oneX A P Θ sy R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR b a X wK hr rfl hw x y hx hy m hZ hs hb
     let T₁:= mural (viewW S R (hw.trans (hy.trans hk))) (evenW S R hp _) (Column.pillar S R x N); let Xv:Stud (S.side R N) 6:= χ; let Yv:Stud (S.side R N) 6:= η
     rw [Vista.ado A R0 _ X _ _ rfl hk] at h
     change topH T₁ A.regulator (Xv - Yv) y ≤ Wp at h
     have hKχ: topH T₁ A.regulator (Yv-Xv) y ≤ Wp:= le_trans (le_of_eq (by rw [show Yv-Xv= (-1:ℂ) • (Xv-Yv) from (by rw [neg_one_smul, neg_sub]),Lyre.top_spin]; simp : _=Lyre.topH T₁ A.regulator (Xv-Yv) y)) h
     refine ⟨hu.1,hu.2,hV,hQ,hA',?_ ,hKχ,hM⟩
     change topH T₁ A.regulator Yv y ≤ _; have hx': Xv+ (Yv-Xv)= Yv:=by abel
     nth_rw 1 [← hx']
     apply le_trans _ (add_le_add hA' hKχ); apply Goblet.bills_plus A.regulator T₁ y Xv (Yv-Xv) hV _ ⟨_,hQ⟩ _ hb
     · rw [sub_eq_add_neg]; exact hu.1.add (Goblet.postsNeg hV)
     rw [sub_eq_add_neg]; exact ⟨q,fun i=> (hu.2 i).add (Goblet.homNeg (x:=Xv) (hQ i))⟩
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.activeQ
