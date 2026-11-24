import YM.Plateau.Rime
import YM.Plateau.Urso
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
local notation "Zℓ"=> sharpM S L Hp z i
local notation "QvG" i:arg=> tokenP i R0
variable (M₁ M₂:Stokes d→ Massive.UV.Label d)
variable (hm:∀ t:Stokes d, GlyphV (H.F t) D hD∈Ω)(hs:∀ t: Stokes d,GlyphV (opposite sym timeAxis (H.F t)) D hD ∈ Ω)
variable (wK m q₀:ℕ)(H':ℝ)(μ: Averaging)
variable (hΓ:Ibis.Tier S L Hp z i ℓ j₀ p wK)(hC:Ibis.Promises L Hp wK Uq m K q₀ ε v H' z)(hJ₁:∀ j:Stokes d,Vista.TicketZ A P Θ R0 εr base Qv none (GlyphV (opposite sym timeAxis (H.F j)) D hD) (M₁ j))(hJ₂:∀ j:Stokes d,Vista.TicketZ A P Θ R0 εr base Qv μ (GlyphV (H.F j) D hD) (M₂ j))
variable (hL:0 < ε) (hv:0<v) (hHt:1≤ H')(hc:∀ i j:Stokes d,Ibis.Faucet ε v (berth sym H hD i j) H')
variable (hKing: ∀ X∈Ω, Tarot.Vista.kingT ((P.display Y Θ sym U base).stencil X.width) ≤ ratioTo S N ℓ*m)(h0:0 ≤ A.regulator.β)(hn:2*(v*measureV L Hp.e z)<((S.side R ℓ).val:ℝ))(hhN:4 ≤(S.side R N).val)(hz:0< A.regulator.Z)(hP:2 ≤ K)
variable (hE:ε ≤ J.e)(hu:J.v ≤ v)(hε: Ibis.minorV L q₀ z ≤ J.ε/8)


include hL hv hP hhN hE hu hJ₁ hKing hC hΓ hz h0 hR hs hn
open Intag Massive.Needle QCD.Plum
open QCD.Acre.Stratum.MarchQ.Suburb
local notation "XP" => marginM S Uq p ℓ +102+m
local notation "Gp"=> Dial.rateB L wK z+ Dial.worthA L Hp z
set_option maxHeartbeats 820000
lemma minst (x:Cover)(F:Insertion (S.side R N) 6) (δ:ℝ)(h:screen S ℓ (sharpM S L Hp z i) x∈closedBall J.a J.l)(hh:∀ (z:Site (S.side R ℓ))(u:Site (S.side R p)), wrap (S.side R ℓ) x ∈ (mural (viewW S R hΓ.ascend.le) (evenW S R hp p) z).margin u (marginM S Uq p ℓ+102+m) → Gold A.regulator (Column.sky S R p N (hΓ.ascend.le.trans (hΓ.above.le.trans hk)) (evenW S R hp _) z) u F δ)(t:Stokes d) : let v':= liftN hD R0 (opposite sym timeAxis (H.F t)) (M₁ t); let Op := Massive.Patria.Depth.Bloom P d (S.side R N) 0 (Qv d none v'); ‖A.regulator.average (Op * F)‖ ≤ (Gp)*δ :=by
     intro v' Op
     obtain ⟨u,y,hx,hp',hQ⟩:= readyY sym H J L Hp z Uq j₀ ℓ K ε v hp wK m q₀ H' hΓ hC hL hv hn hP hE hu x h -- arg
     let Z:= opposite sym timeAxis (H.F t); let T:= GlyphV Z D hD; let T0:= (Column.sky S R p N (hΓ.ascend.le.trans (hΓ.above.le.trans hk)) (evenW S R hp _) u); have hV:(T).material≠0:= fun h=> living H t ((sym.adj d timeAxis).injective (h.trans (map_zero _).symm))
     have hU:0<Uq:=by have ht:=hC.permit; omega
     obtain ⟨hF,hW,_,_,_,hG,h₁,h₂⟩:= Vista.activeQ A P Θ sym Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR 0 none T (M₁ t) wK hC.fonts hΓ.view hΓ.ascend.le u (y 0) (hs t) hΓ.above.le hV (hJ₁ t).harvest m hp' hU (hKing T (hs t)) ⟨rfl,hhN,rfl,h0,hz.ne'⟩
     have he : Vista.hYcheck P R0 ℓ Qv none T (M₁ t) 0=Op:=by
          unfold Vista.hYcheck; rw [smul_zero]; unfold Op v' Vale.liftN; rw [map_smul,map_smul]; rfl
     rw [he] at hF hW hG; have hT : Gold A.regulator T0 (y 0) Op (Gp):= Gold.mono (coin hF ⟨_,hW⟩) hG; have hX:=hh u (y 1) hQ; let W:Fin 2→Insertion (S.side R N) 6:=![Op,F]; let V:Fin 2→ℝ:=![Gp,δ]; have ht:= Gold.value (T:=T0) y hx W V (Fin.forall_fin_two.mpr ⟨hT,hX⟩) rfl rfl h0 hhN hz.ne'
     simpa only [Fin.prod_univ_succ,List.ofFn_zero,List.ofFn_succ,List.prod_nil,List.prod_cons,mul_one,Finset.univ_eq_empty,Finset.prod_empty,V,W, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] using ht -- exact defeq
end YM.Intag.Vale
#print axioms YM.Intag.Vale.minst
