import YM.Plateau.Mallet
import YM.ValeK.Wests
import YM.Plateau.Firth
import YM.ValeK.Aster
import YM.Alum.Pulps
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Vale
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
open RG
open Poised Poised.Plans Poised.Plans.Stamp
variable {Vb:YM.Source.Hol su}(P: Lining.Temper.Collage.Exhibit Vb) (Θ: Massive.SourceRead.TaperHol)(sym:RawSym)(Y: Massive.Sequence)(U:Lining.Temper.Collage.Exhibit.CoreMix)
variable {S:Scheme}{R:Side}{i p j N:ℕ}(A: Massive.Run S N R 6)
open Lattice Wilson Cells YM.Next.Rank.Station Ibis
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open Tarot Tarot.Vista Pilgrim Tess Hymnal MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open QCD.Acre.Stratum.MarchQ.Suburb.Sapphire QCD.Acre.Stratum.MarchQ.Suburb.MintV Metric
open Arise Parcel
set_option quotPrecheck false
variable {d D:ℕ}
variable (H:Laurel d)(J:Landing sym H)(hD:d ≤ D)
variable (R0:Vista (S.side R i) D)(N₀:ℕ)(L:Side)(Ω:Finset (Glyph D))(Hp:Dial D)(z:ℝ)(Dk Uq j₀ ℓ K:ℕ)(ε v εr Xv:ℝ)(hB:ℕ→BudgetPoint)(pv:ℕ→ℝ)(base:ℕ→ℕ)(Qv:∀ d,PatchMix d)(hp:Even R.val)(hk:i≤ N)
variable (hR:Vista.RoofV A R0 hk hp sym Ω Uq K ε v Xv Hp L z j₀ ℓ Θ P εr Dk hB pv base Qv)
local notation "F" t:arg=> GlyphV (H.F t) _ hD
local notation "Zℓ"=> sharpM S L Hp z i
local notation "QvG" i:arg=> tokenP i R0
variable (M₁ M₂:Stokes d→ Massive.UV.Label d)
variable (hm:∀ t:Stokes d, GlyphV (H.F t) D hD∈Ω)(hs:∀ t: Stokes d,GlyphV (opposite sym timeAxis (H.F t)) D hD ∈ Ω)
variable (wK m q₀:ℕ)(H':ℝ)(μ: Averaging)
variable (hΓ:Ibis.Tier S L Hp z i ℓ j₀ p wK)(hC:Ibis.Promises L Hp wK Uq m K q₀ ε v H' z)(hJ₁:∀ j:Stokes d,Vista.TicketZ A P Θ R0 εr base Qv none (GlyphV (opposite sym timeAxis (H.F j)) D hD) (M₁ j))(hJ₂:∀ j:Stokes d,Vista.TicketZ A P Θ R0 εr base Qv μ (GlyphV (H.F j) D hD) (M₂ j))
variable (hL:0 < ε) (hv:0<v) (hHt:1≤ H')(hc:∀ i j:Stokes d,Ibis.Faucet ε v (berth sym H hD i j) H')
variable (hKing: ∀ X∈Ω, Tarot.Vista.kingT ((P.display Y Θ sym U base).stencil X.width) ≤ ratioTo S N ℓ*m)(h0:0 ≤ A.regulator.β)(hn:2*(v*measureV L Hp.e z)<((S.side R ℓ).val:ℝ))(hhN:4 ≤(S.side R N).val)(hz:0< A.regulator.Z)(hP:2 ≤ K)
variable (hE:ε ≤ J.e)(hu:J.v ≤ v)(hε: Ibis.minorV L q₀ z ≤ J.ε/8)


open YM.Massive.Needle YM.Massive.Patria GaugeP Massive.Tarn.Choir.Measures
noncomputable abbrev lark (b:Cover)(t:ℝ):E4:= digit t b
-- native λ spacing `resolution` into pinned J work. one Cover independent of k.Frame.
variable {Kz Vθ:ℝ}
include hΓ J
local notation "θx"=> sharpM S L Hp z i
local notation "κ"=> measureV L Hp.e z
noncomputable abbrev pinL (sym:RawSym)(H:Laurel d)(J:Landing sym H)(L:Side)(Hp:Dial D)(z:ℝ) : Cover := bead (measureV L Hp.e z)⁻¹ J.a
lemma wheelK (Yz:Massive.Sequence) (hQ:S=Yz.S)(hv:2*κ⁻¹≤ J.l)(ht:200*κ⁻¹ < J.e)(hP:Yz.Path Kz Vθ): let b:= pinL sym H J L Hp z; screen S ℓ (sharpM S L Hp z i) b∈ closedBall J.a J.l ∧ ∃ A:Set E4, IsCompact A∧0 ∉ A∧ Pasture Yz ℓ b A :=by
    intro b; let y:= screen S ℓ θx b; have hz:0 < κ:= χone ..; have h₁:y∈closedBall J.a J.l:= by unfold y screen; rw [hΓ.shadows]; exact (smoothV (inv_pos.mpr hz) J.a).trans hv
    refine ⟨h₁,?_⟩; let R:= Yz.S.spacing ℓ; let P:= digit R b; have hΩ:= J.pose y h₁; have hX:2*J.e≤ ‖y‖:=by have h:‖y timeAxis‖≤‖y‖:= PiLp.norm_apply_le y _; have hz:= hΩ.2.1 timeAxis; rw[Real.norm_of_nonneg (by linarith only [hz,J.far])] at h; exact hz.trans h -- check order
    let D':= 200*R; let C:= Metric.closedBall P D'; have hc : 0 ∉ C:=by
         have hν: R=κ⁻¹ * θx:= (by unfold R; rw [←hQ]; exact (div_eq_iff (Tier.realH ..).ne').1 hΓ.shadows)
         have hP' : P=θx • y:=by unfold P y screen; rw [hΓ.shadows, smul_smul, mul_comm,← hν]; rfl
         have hp0:0 < θx:=Tier.realH ..
         have hη:D'< ‖P‖:=by unfold D'; rw [hν,hP',norm_smul,Real.norm_of_nonneg hp0.le]; nlinarith only [hp0, ht,hX,J.far]
         intro z; exact not_le_of_gt hη (by rw [←dist_zero_left P]; exact z)
    refine ⟨C,isCompact_closedBall _ _,hc,?_⟩; filter_upwards [hP.uv.tendsto_atTop.eventually_ge_atTop ℓ] with i hi z hz
    have hp':= port i ℓ (show ℓ≤ Yz.N i from hi) z hz; change dist (digit (Yz.S.spacing (Yz.N i)) (ratioTo Yz.S (Yz.N i) ℓ • b+z)) P ≤ D'; rw [digit_plus,← gears (show ℓ≤Yz.N i from hi),dist_eq_norm]; rw [show digit (Yz.S.spacing ℓ) b=P from rfl, add_comm P, add_sub_cancel_right]; exact hp'
omit hΓ J
include hΓ hC hp hn hE hu hv hL hP J
lemma readyY (x:Cover)(hx:screen S ℓ (sharpM S L Hp z i) x ∈ Metric.closedBall J.a J.l) : let hj:=hΓ.ascend.le; let Xℓ:=marginM S Uq p ℓ+102+m; ∃ (z:Site (S.side R ℓ))(f:Fin 2→ Site (S.side R p)), Injective f ∧ wrap _ 0∈ (mural (viewW S R hj) (evenW S R hp p) z).margin (f 0) Xℓ ∧ wrap _ x∈ (mural (viewW S R hj) (evenW S R hp p) z).margin (f 1) Xℓ:=by
     intro hj Xℓ; let X := (![0,x]:Fin 2 → Cover); let t:=screen S ℓ (sharpM S L Hp z i); let y:=t ∘ X; have hy:y=![0,t x]:=by ext1 k; fin_cases k; change screen _ _ _ (0:Cover)=0; unfold screen; rw [show Massive.vector 0=0 from (by ext a; simp [Massive.vector]),smul_zero]; rfl
     have hT:y∈ flats (Fin 2) ε v:= hy.symm ▸ Ibis.puff _ _ _ (J.pose (t x) hx).1 _ _ _ 0 (by rw[sub_self,norm_zero]) (by linarith only[hE,hL]) (by linarith only[hu,hv])
     obtain ⟨x',f,h₁,h₂,h₃⟩:= Ibis.slant hΓ hC.hue hp X (fun i=> ((perim ε v y hT hv.le i).trans (by linarith only [hv]: v/2 ≤ v))) (Ibis.iris ε v y hT hv.le) hn (hΓ.lower.trans hj) hj (by simpa using hP)
     exact ⟨x',f,h₁,padding _ _ _ _ _ (viewOdd ..) (h₃ 0) (by unfold Xℓ; omega),padding _ _ _ _ _ (viewOdd ..) (h₃ 1) (by unfold Xℓ; omega)⟩
end YM.Intag.Vale
#print axioms YM.Intag.Vale.readyY
#print axioms YM.Intag.Vale.wheelK
