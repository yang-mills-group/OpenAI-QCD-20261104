import YM.Alum.Alu
import YM.Alum.Lawn
import YM.Alum.Lawn
import YM.Alum.Tines
import YM.Alum.Daisy
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
variable (u:ℕ)(hX:X.material≠0)
-- exact proof source abilities.ALL alignment array.For a given reference and View.Small φ uncertain. Tally bindings.
-- exact proof source abilities.ALL alignment array.For a given reference and View.Small φ uncertain. Tally bindings.
-- actual point Xi any lifts.Con full.Thermal orientation. Pay at fine interior.By reconciliation.R.T
local notation "Φ" => Dial.worthA L Hp z
local notation "Fw"=> Qv X.width none G
local notation "G!"=> bornC (N:=N) P X R0 (Qv X.width none G)
set_option quotPrecheck false
noncomputable def softerT (S:Scheme)(ℓ p N Uq m:ℕ):= ratioTo S N ℓ*(marginM S Uq p ℓ+104+m) -- ≥ m+1 Upper.
include hx ht hw hR hy hr hX
variable (m:ℕ)(hs:0<Uq)(hG: TicketZ A P Θ R0 εr base Qv none X G)(hφ:Goblet.Smoke (Column.sky S R p N (hw.trans (hy.trans hk)) (evenW S R hp p) x) A.regulator) (hV:kingT ((P.display Y Θ sy U base).stencil X.width) ≤ ratioTo S N ℓ * m)
open Goblet
include hs hG hφ hV
lemma throughY (htX: wrap _ b∈ (Column.sky S R p N (hw.trans (hy.trans hk)) (evenW S R hp p) x).margin y (softerT S ℓ p N Uq m)) : Base (Column.sky S R p N (hw.trans (hy.trans hk)) (evenW S R hp p) x) y 0 ((G!) b) ∧ Fence ((Column.sky S R p N (hw.trans (hy.trans hk)) (evenW S R hp p) x).chamber y) ((G!) b) ∧ (∀ W, Hom (polarity X.spin) ((G!) b W))∧ topH (T) A.regulator ((G!) b) y ≤ (Go)+Φ:=by
       let y' : UV.Label X.width:= (tokenP X R0:ℂ) • Fw; let Z(c:Cover):Insertion (S.side R N) 6:= Bloom P X.width (S.side R N) c y'
       have hx'(c): (G!) c=Z c:= by unfold Z bornC y'; rw[map_smul] -- arg
       have hh:ℓ ≤ N:=hy.trans hk; have hpq:Odd (ratioTo S N p):= odd_to (hw.trans hh)
       have hQ:moored y'.val (polarity X.spin):=by unfold moored y'; change parityAct (_ • _) = _ • (_ • _); rw [map_smul,hG.caliber];exact smul_comm .. -- hG.caliber unfold
       let r:= Vp (hw.trans hh); let ν:= Column.pillar S R x N; let T₁:= mural r H₀ (ν+r.embed y)
       let b₀:= marginM S Uq p ℓ+102+m; let l:= ratioTo S N ℓ; let k:=l*b₀; let s:=softerT S ℓ p N Uq m
       have hb:k+(l+1) ≤ s:=by unfold s k softerT; change _ ≤ l*_; have h:marginM S Uq p ℓ+104+m=b₀+2:=(by unfold b₀; omega); rw [h, mul_add l b₀ 2]; have hp:0<l:= (odd_to hh).pos; omega
       have hm: kingT ((P.display Y Θ sy U base).stencil X.width)≤k:= hV.trans (Nat.mul_le_mul_left l (Nat.le_add_left ..))
       have hrr (s:ℕ)(y':Site (S.side R N)): y'∈ (T).margin y s ↔ y'∈ T₁.margin 0 s:= (show _ from (by have h:=Goblet.margV r H₀ ν y 0 hpq y' s; rw[add_zero] at h; exact h))
       have hl(b:Cover)(hx:wrap _ (l • b)∈ T₁.margin 0 k):wrap _ b ∈ (Γ).margin y b₀:=by
              let f:= Vp hh; apply (stepSpan g f r x (wrap _ b) y H₀ (viewOdd S R hw) (viewOdd S R hh) b₀).mpr; have hv:ν=f.embed x:=dif_pos hh; rw [←hv,Ratio.embed_wrap]; exact (hrr k _).2 hx -- k exact
       have hZ:= kingFlow P Θ sy Y U base b (T) y _ y' q hQ htX (le_trans hm (by omega:k ≤ s)) rfl
       simp_rw[hx']; change Base (T) y 0 (Z b) ∧ Fence ((T).chamber y) (Z b)∧ (∀ W, Hom q (Z b W))∧ topH (T) A.regulator ⇑(Z b) y ≤ Go+Φ
       have hr0(c:Cover): topH (T) A.regulator (Z c) y= floorL T₁ A.regulator.average A.regulator (Z c) 0 :=by
               have he:Potion (Z c):=⟨q,Hub.fade _ sy (Massive.Patria.Depth.stays P Θ Y base sy U _) y' q hQ _⟩
               have h:= Goblet.repointed r H₀ ν y A.regulator (Z c) 0 he; rw[add_zero] at h; exact h.trans (sprouts A.regulator T₁ _ _ hφ.real).symm -- argument order
       refine ⟨hZ.1,hZ.2.1,hZ.2.2,?_⟩; rw[hr0]; apply Hub.strictH T₁ A.regulator (Bloom P X.width) sy (Massive.Patria.Depth.stays P Θ Y base sy U _) rfl hφ.real y' q hQ hφ.pos hφ.cycle b _ l (odd_to hh|>.pos) (k:=k) (padding r _ _ _ _ hpq ((hrr s _).1 htX) ((show l+1+k=k+(l+1) by omega).trans_le hb)) (fun x h=>?_)
       · intro c he; have hz:= activeQ A P Θ sy Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR c none X G wK hr ht hw x y hx hy hX hG.harvest m (hl c he) hs hV hφ -- shadow!, change rr
         have he: topH (T) A.regulator ( (G!) (l • c)) y ≤ Go+Φ := hz.2.2.2.2.2.1; rw[hx',hr0] at he; exact he
       exact (kingFlow P Θ sy Y U base _ T₁ _ k y' q hQ h hm rfl).1
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.throughY
