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

include hE hu hε hHt hc hn h0 hhN hz hP hL hv hm hs hR hJ₁ hJ₂ hC hΓ hKing

-- Mixed second leg pricing and actual margin grants.
lemma paging (x:Cover)(h:screen S ℓ (sharpM S L Hp z i) x∈ closedBall J.a J.l)(t u:Stokes d): let Q(w:Averaging)(p:Label d)(b:Cover):= Massive.Patria.Depth.Bloom P d (S.side R N) b (Qv d w p); ‖A.regulator.average (Q none (liftN hD R0 (opposite sym timeAxis (H.F t)) (M₁ t)) 0 * CardsT.checkedT μ (ratioTo S N ℓ) (Q μ (liftN hD R0 (H.F u) (M₂ u))) x) - ΦGram sym H (basis timeAxis) t u‖ ≤ J.ε:=by
     intro Q; let f:= berth sym H hD t u; let Γ:= ![M₁ t,M₂ u]; let a:= basis timeAxis; let y:= screen S ℓ (sharpM S L Hp z i) x; have hY:= J.pose y h; let X := (![0,x]:Fin 2 → Cover); let V:Fin 2→ Averaging:=![none,μ]
     have hk:∀ k:Stokes d, (opposite sym timeAxis (H.F k)).mark≠0:=fun i h=> living H i ((sym.adj d timeAxis).injective (h.trans (map_zero _).symm))
     have he(V:Averaging)(B:Text d)(z:Label d): Vista.bornC (N:=N) P (GlyphV B _ hD) R0 (Qv d V z)= Q V (liftN hD R0 B z):=by funext v; unfold Vista.bornC Q liftN; rw[map_smul,map_smul]; rfl
     have hΦ(k:Fin 2): Vista.TicketZ A P Θ R0 εr base Qv (V k) (f k) (Γ k):=by fin_cases k; exact hJ₁ t; exact hJ₂ u
     have hy:(screen S ℓ (sharpM S L Hp z i) ∘ X)=![0,y]:=by ext1 k; fin_cases k; change screen _ _ _ (0:Cover)=0; unfold screen; rw[show Massive.vector 0=0 from (by ext a; simp [Massive.vector]),smul_zero]; rfl
     have hV:(screen S ℓ (sharpM S L Hp z i) ∘ X)∈flats (Fin 2) (2*ε) (v/2):= hy.symm ▸ Ibis.puff _ _ _ hY.1 _ _ _ 0 (by rw[sub_self,norm_zero]) (by linarith only[hE,hL]) (by linarith only[hu,hv])
     have h₁:= Vista.clubG (p:=p) A P Θ sym Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp ‹_› hR wK 2 m f V Γ X (fun i=> by fin_cases i; exact hs t;exact hm u) (fun j=> by fin_cases j; exact hk t;exact living H u) hΦ hKing q₀ H' hΓ hC hL hv hHt (hc ..) h0 hn hhN hz.ne' hP hV -- args
     rw [hy,show candle f ![0,y]= _ from berth_g sym H hD t u y,List.ofFn_succ,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_cons,List.prod_nil,mul_one] at h₁; let xh:=Q none (liftN hD R0 (opposite sym timeAxis (H.F t)) (M₁ t)) 0; let yh:=CardsT.checkedT μ (ratioTo S N ℓ) (Q μ (liftN hD R0 (H.F u) (M₂ u))) x
     have hx : Vista.yeast (N:=N) P R0 ℓ Qv f V Γ X 0=xh:=by
          change ⇑(Averaging.filter (V 0) (ratioTo S N ℓ) (Vista.bornC (N:=N) P (GlyphV (opposite sym timeAxis (H.F t)) D hD) R0 (Qv d none (M₁ t))) (ratioTo S N ℓ • (0:Cover)))= _; rw [he, smul_zero]; rfl
     have heY: Vista.yeast (N:=N) P R0 ℓ Qv f V Γ X 1=yh:=by
          change ⇑(Averaging.filter μ (ratioTo S N ℓ) (Vista.bornC (N:=N) P (GlyphV (H.F u) D hD) R0 (Qv d μ (M₂ u))) (ratioTo S N ℓ • x))= _; rw [he]; rfl
     let U':= A.regulator.average (xh*yh); have hz: ‖U'-ΦGram sym H y t u‖ ≤ J.ε/4:=by
          change ‖Lyre.valueH A.regulator ((Vista.yeast (N:=N) P R0 ℓ Qv f V Γ X 0)*(Vista.yeast (N:=N) P R0 ℓ Qv f V Γ X 1))-ΦGram sym H y t u‖ ≤ _ at h₁; rw[hx,heY] at h₁; apply le_trans h₁; linarith only [J.light,hε]
     exact (norm_sub_le_norm_sub_add_norm_sub U' (ΦGram sym H y t u) _).trans (by linarith only [hz,(hY.2.2 t u).le,J.light])
end YM.Intag.Vale
#print axioms YM.Intag.Vale.paging
