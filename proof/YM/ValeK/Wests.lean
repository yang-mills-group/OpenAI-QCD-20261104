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
noncomputable def west(h:d ≤ D)(i j:Stokes d)(k:Fin 2):Text d:= (![opposite sym timeAxis (H.F i), H.F j]:Fin 2 → Text d) k
noncomputable def berth(h:d ≤ D)(i j:Stokes d)(k:Fin 2):Glyph D:= GlyphV (west sym H h i j k) D h
local notation "Bτ"=>berth sym H hD
local notation "Fτ" i:arg=> GlyphV (opposite sym timeAxis (H.F i)) D hD
lemma berth_g(i j:Stokes d)(y:E4):Ibis.candle (berth sym H hD i j) ![0,y] = ΦGram sym H y i j:=by
    unfold ΦGram; apply congr_arg (UV.Free.wick (fun _ : Fin 2=>d) _); ext1 i; fin_cases i<;>rfl
local notation "Zℓ"=> sharpM S L Hp z i
local notation "QvG" i:arg=> tokenP i R0
variable (M₁ M₂:Stokes d→ Massive.UV.Label d)
variable (hm:∀ t:Stokes d, GlyphV (H.F t) D hD∈Ω)(hs:∀ t: Stokes d,GlyphV (opposite sym timeAxis (H.F t)) D hD ∈ Ω)
variable (wK m q₀:ℕ)(H':ℝ)
variable (hΓ:Ibis.Tier S L Hp z i ℓ j₀ p wK)(hC:Ibis.Promises L Hp wK Uq m K q₀ ε v H' z)(hJ₁:∀ j:Stokes d,Vista.TicketZ A P Θ R0 εr base Qv none (GlyphV (opposite sym timeAxis (H.F j)) D hD) (M₁ j))(hJ₂:∀ j:Stokes d,Vista.TicketZ A P Θ R0 εr base Qv none (GlyphV (H.F j) D hD) (M₂ j))
variable (hL:0 < ε) (hv:0<v) (hHt:1≤ H')(hc:∀ i j:Stokes d,Ibis.Faucet ε v (berth sym H hD i j) H')
variable (hKing: ∀ X∈Ω, Tarot.Vista.kingT ((P.display Y Θ sym U base).stencil X.width) ≤ ratioTo S N ℓ*m)(h0:0 ≤ A.regulator.β)(hn:2*(v*measureV L Hp.e z)<((S.side R ℓ).val:ℝ))(hhN:4 ≤(S.side R N).val)(hz:0< A.regulator.Z)(hP:2 ≤ K)
variable (hE:ε ≤ J.e)(hu:J.v ≤ v)(hε: Ibis.minorV L q₀ z ≤ J.ε/8)
noncomputable def liftN (Q:Text d)(b:Label d):Label d:= (tokenP (GlyphV Q D hD) R0:ℂ) • b
include hE hu hε hHt hc hn h0 hhN hz hP hL hv hm hs hR hJ₁ hJ₂ hC hΓ hKing
lemma perusing(x:Cover) (h:screen S N (sharpM S L Hp z i) x∈ closedBall J.a J.l)(t u:Stokes d): let Q (p:Label d)(b:Cover):= Massive.Patria.Depth.Bloom P d (S.side R N) b (Qv d none p); ‖A.regulator.average (Q (liftN hD R0 (opposite sym timeAxis (H.F t)) (M₁ t)) 0 * Q (liftN hD R0 (H.F u) (M₂ u)) x) - ΦGram sym H (basis timeAxis) t u‖ ≤ J.ε*3/4:=by
     intro Q; let f:= berth sym H hD t u; let Γ:= ![M₁ t,M₂ u]; let a:= (basis timeAxis); let y:= screen S N (sharpM S L Hp z i) x; have hY:= J.pose y h
     have hk:∀ k:Stokes d, (opposite sym timeAxis (H.F k)).mark≠0:=fun i h=> living H i ((sym.adj d timeAxis).injective (h.trans (map_zero _).symm))
     have he(t:Cover)(B:Text d)(z:Label d): Vista.bornC (N:=N) P (GlyphV B _ hD) R0 (Qv d none z) t = Q (liftN hD R0 B z) t:=by unfold Vista.bornC Q liftN; rw[map_smul,map_smul]; rfl
     have hΦ(k:Fin 2): Vista.TicketZ A P Θ R0 εr base Qv none (f k) (Γ k):=by fin_cases k; exact hJ₁ t; exact hJ₂ u
     have hT:= Vista.tussle (p:=p) A P Θ sym Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp ‹_› hR wK m f Γ (fun i=> by fin_cases i; exact hs t;exact hm u) (fun j=> by fin_cases j; exact hk t;exact living H u) hΦ hKing q₀ H' hΓ hC hL hv hHt (hc ..) h0 hn hhN hP hz x (Ibis.puff _ _ _ hY.1 _ _ _ 0 (by rw[sub_self,norm_zero]) (by linarith only[hE]) (by linarith only[hu])) (fun a'=>le_trans (show _ ≤2*J.e from by linarith only [hE]) (hY.2.1 a')) -- args
     let c := A.regulator.average (Q (liftN hD R0 (opposite sym timeAxis (H.F t)) (M₁ t)) 0 * Q (liftN hD R0 (H.F u) (M₂ u)) x); change ‖c- _‖ ≤_; have h1: ‖c-ΦGram sym H y t u‖ ≤ J.ε/8:=by rw [←berth_g _ _ hD]; unfold c; rw[← he 0 _ _,← he x _ _]; exact hT.trans hε
     exact (norm_sub_le_norm_sub_add_norm_sub c _ _).trans ((add_le_add h1 (hY.2.2 t u).le).trans (by linarith only[J.light])) -- signature
end YM.Intag.Vale
#print axioms YM.Intag.Vale.perusing
