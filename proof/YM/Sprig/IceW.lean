import YM.Sprig.Icing
import YM.Alum.Soda
import YM.Sprig.Folds
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
local notation "polarZ" => polarity X.spin
variable (ht:p=Dial.viewAt L Hp z j₀ wK)(hw:p ≤ ℓ) (x:Site (S.side R ℓ))(y:Site (S.side R p))(hx:X∈Ω) (hm: moored (Qv X.width a G).val (polarity X.spin)) (hy:ℓ≤ i)
local notation "g" =>viewW S R hw
local notation "H₀"=>evenW S R hp p
local notation "Γ"=>mural (viewW S R hw) H₀ x
variable (u:ℕ)(hX:X.material≠0)
-- exact proof source abilities.ALL alignment array.For a given reference and View.Small φ uncertain. Tally bindings.
-- exact proof source abilities.ALL alignment array.For a given reference and View.Small φ uncertain. Tally bindings.
-- Genuine readings: informe from a single finite preparation with same linear matches of all labels.
variable (w m n q:ℕ)
-- Zcurve.L inputs
variable (Z:∀ d,Label d →ₗ[ℂ] Label d)(Yq:Fin n → Glyph D)
set_option quotPrecheck false
-- over uses means.Discrete apertures post support independent.
noncomputable abbrev spiral {P_:YM.Source.Hol su}(Uv:Lining.Temper.Collage.Exhibit P_)(S':Scheme)(N:ℕ)(R:Side)(Qv:∀ d,PatchMix d)(Z:∀ d,Label d→ₗ[ℂ] Label d)(X:Glyph D)(x:Cover): Insertion (S'.side R N) 6:= Massive.Patria.Depth.Bloom Uv X.width (S'.side R N) x (Qv X.width none (Z X.width X.material))
local notation "T∗"=> Ibis.sharpM S L Hp z i
local notation "Π" j:arg=> Ibis.screen S j T∗
local notation "χ"=> (Z)
open Goblet Ibis
variable (hΩ:∀ j,Yq j∈Ω)(hΔ:∀ j,(Yq j).material≠0)(hKing:∀ X∈ Ω, kingT ((P.display Y Θ sy U base).stencil X.width) ≤ ratioTo S N ℓ*m)
variable (H:ℝ)(h1:1 ≤H)(hH:Ibis.Faucet ε v Yq H)
variable (ha:∀ d:ℕ,d ≤ D→∀ p:UV.Label d,Sprig.Attest A R0 Θ (base d) p (Z d p))(hΓ:Tier S L Hp z i ℓ j₀ p w)(hC:Promises L Hp w Uq m K q ε v H z)
variable (hz:0 < ε)(hv:0<v)(hN:2*(v*measureV L Hp.e z)<((S.side R ℓ).val:ℝ))(hn:n≤ K)
include hΩ hΔ hΓ ha hC hR
variable (xo:Fin n→ Cover)
local notation "Δ"=> ratioTo S N ℓ
lemma constantP :∃ f: ∀ j,Label (Yq j).width,(∀ j,TicketZ A P Θ R0 εr base Qv none (Yq j) (f j)) ∧∀ j,spiral P S N R Qv Z (Yq j)= bornC (N:=N) P (Yq j) R0 (Qv (Yq j).width none (f j)):=by
     choose t hf using fun j:Fin n=> Vista.cheers A P Θ sy R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR none (Yq j) w hC.fonts (hΩ j) (hΔ j) (hΓ.view ▸ hΓ.ascend.le) (hΓ.above.le.trans hk) hC.permit
     refine ⟨t,hf,fun j=>?_⟩; have h := Sprig.stark A R0 Θ P Qv εr base _ _ _ (ha _ (Yq j).raised) (hf j); rw [Sprig.stampAt]; change _=(fun x:Cover=>Massive.Patria.Depth.Bloom P _ _ x (Qv (Yq j).width none (Sprig.tallyPt R0 (Yq j) (t j)))); rw[h]
include hz hv h1 hH hKing hN hn
open scoped ComplexOrder
variable (hzA:0<A.regulator.Z)(h0:0 ≤ A.regulator.β)(hR':4 ≤ (S.side R N).val)
include hzA h0 hR'
#check constantP
noncomputable abbrev stampZ (S:Scheme)(N:ℕ)(R:Side)(Z:∀ d,Label d→ₗ[ℂ]Label d)(X:Fin n→ Glyph D)(x:Fin n→ Cover)(j:Fin n):Insertion (S.side R N) 6:= spiral P S N R Qv Z (X j) (ratioTo S N ℓ • x j)
local notation "Go"=> stampZ P ℓ Qv n S N R Z Yq xo
lemma cheersG (hc: screen S ℓ (sharpM S L Hp z i) ∘ xo∈ flats (Fin n) (2*ε) (v/2)): ‖ A.regulator.average (List.ofFn (stampZ P ℓ Qv n S N R Z Yq xo)).prod - candle Yq (screen S ℓ T∗ ∘ xo)‖ ≤ minorV L q z:=by
     obtain ⟨f,hZ,Hg⟩:= constantP A P Θ sy R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR w m n q Z Yq hΩ hΔ H ha hΓ hC
     have ht:= clubG A P Θ sy Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR w n m Yq (fun _=>none) f xo hΩ hΔ hZ hKing q H hΓ hC hz hv h1 hH h0 hN hR' hzA.ne' hn hc
     let Ξ:=Go
     rw [Goblet.knownV]; rw [show ⇑(List.ofFn (Go)).prod=(List.ofFn (Vista.yeast (N:=N) P R0 ℓ Qv Yq (fun _=>none) f xo)).prod from ?_]; exact ht.trans (div_le_self (grow L z q).le (by norm_num))
     let F(i:Fin n) := stampZ P ℓ Qv n S N R Z Yq xo i; let X(i:Fin n) : Stud (S.side R N) 6 := Vista.yeast (N:=N) P R0 ℓ Qv Yq (fun _=>none) f xo i
     have h(i:Fin n) : ⇑(F i)=X i:=by unfold F stampZ; rw [Hg i]; rfl
     suffices T : ∀ l:List (Fin n), ⇑(l.map F).prod=(l.map X).prod by rw [List.ofFn_eq_map,List.ofFn_eq_map]; apply T
     intro l; induction l with| nil=>rfl|cons i l ih=>simp only [List.map_cons,List.prod_cons, ContinuousMap.coe_mul,h,ih]
lemma roomP (hv': screen S N (sharpM S L Hp z i) ∘xo∈ flats (Fin n) (2*ε) (v/2)): ∃ (a:Site (S.side R ℓ))(q:Fin n→Site (S.side R p)), Injective q∧ (∀ i', wrap _ (xo i')∈ (Column.sky S R p N (hΓ.ascend.le.trans (hΓ.above.le.trans hk)) (evenW S R hp p) a).margin (q i') (Vista.softerT S ℓ p N Uq m))∧∀ i', let T:= Column.sky S R p N (hΓ.ascend.le.trans (hΓ.above.le.trans hk)) (evenW S R hp p) a; let W:= spiral P S N R Qv Z (Yq i') (xo i'); Fence (T.chamber (q i')) (⇑W) ∧ (∀ V, Hom (polarity (Yq i').spin) (W V)) ∧ topH T A.regulator (⇑W) (q i') ≤ reserved L Hp w z:=by
      obtain ⟨a,Q,hp',ht⟩:= Ibis.flanks hΓ hp xo q hC (hΓ.above.le.trans hk) hv' hN (by simpa using hn) hv
      obtain ⟨f,hZ,Hg⟩:= constantP A P Θ sy R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR w m n q Z Yq hΩ hΔ H ha hΓ hC
      refine ⟨a,Q,hp', ht,fun i'=>?_⟩; rw[Hg i']; intro T W; obtain ⟨h1,h2,h3,h4⟩:= throughY A P Θ sy Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR (xo i') (Yq i') (f i') w hC.fonts hΓ.view hΓ.ascend.le a (Q i') (hΩ i') hΓ.above.le (hΔ i') m (Nat.lt_of_lt_of_le (by norm_num:0 < 2) hC.permit) (hZ i') ⟨rfl,hR',rfl,h0,hzA.ne'⟩ (hKing _ (hΩ i')) (ht i'); exact ⟨h2,h3,h4⟩
lemma clubs_glide (hh:((screen S ℓ (sharpM S L Hp z i))∘xo) ∈ Ibis.flats (Fin n) (2*ε) (v/2))(hi:0<n) : ∃ (x:Site (S.side R ℓ))(hw:j₀ ≤ ℓ)(hp':ℓ ≤ i) (hy_:∀ i' V, Hom (weightsT Yq i') ((⇑(stampZ P ℓ Qv n S N R Z Yq xo i')) V)), let F(i:Fin n) := ⇑(stampZ P ℓ Qv n S N R Z Yq xo i); let V:= ProbeWords Yq (List.finRange n) ((screen S ℓ (sharpM S L Hp z i))∘xo) F hy_; Fence ((Column.sky S R j₀ N (hw.trans (hp'.trans hk)) (evenW S R hp j₀) x).chamber (0:Site (S.side R j₀))) V ∧ Potion V ∧ topH (Column.sky S R j₀ N (hw.trans (hp'.trans hk)) (evenW S R hp j₀) x) A.regulator V (0:Site (S.side R j₀)) ≤ minorV L q z:=by
     obtain ⟨f,hZ,Hg⟩:= constantP A P Θ sy R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR w m n q Z Yq hΩ hΔ H ha hΓ hC
     have hh'(i:Fin n) : ⇑((Go) i)= (Vista.yeast (N:=N) P R0 ℓ Qv Yq (fun _=>none) f xo i):=by unfold stampZ; rw[Hg]; rfl -- HEq parentheses
     -- dependent type proof. case via pointwise eq.
     let X(i:Fin n): Stud (S.side R N) 6:= ⇑(stampZ P ℓ Qv n S N R Z Yq xo i)
     let Y' := Vista.yeast (N:=N) P R0 ℓ Qv Yq (fun _=>none) f xo
     have ht : X=Y':=funext hh'; have hp'' := clubH A P Θ sy Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR w n m Yq (fun _=>none) f xo hΩ hΔ hZ hKing q H hΓ hC hz hv h1 hH h0 hN hR' hzA.ne' hn hh hi (fun _=>rfl)
     obtain ⟨u,wv,hv',hx,hU⟩:=hp''; have hP(i':Fin n) Wt': Hom (weightsT Yq i') (X i' Wt'):=by rw [ht]; exact hx i' Wt'
     refine ⟨u,wv,hv',hP,?_⟩; intro F_ V
     have hh:ProbeWords Yq (List.finRange n) ((screen S ℓ (sharpM S L Hp z i)) ∘xo) X hP = ProbeWords Yq (List.finRange n) ((screen S ℓ (sharpM S L Hp z i)) ∘xo) Y' hx:=by congr 1
     rw[show V= ProbeWords Yq (List.finRange n) ((screen S ℓ (sharpM S L Hp z i)) ∘xo) Y' hx from hh]; exact hU
omit hn hΩ hΔ hH
variable (Y': Fin 2→ Glyph D)(hY:2≤ K)(hΩQ:∀ i,Y' i∈Ω)(hΔQ:∀ i,(Y' i).material≠0)(hHQ:Ibis.Faucet ε v Y' H)
include hΩQ hΔQ hY hHQ
lemma testR (t:Cover)(hf:![0,screen S N (sharpM S L Hp z i) t] ∈ flats (Fin 2) (3*ε) (v/4))(hpV:∀ a:Axis,2*ε ≤ screen S N (sharpM S L Hp z i) t a): ‖ A.regulator.average (spiral P S N R Qv Z (Y' 0) 0 * spiral P S N R Qv Z (Y' 1) t) - candle Y' ![0,screen S N (sharpM S L Hp z i) t]‖ ≤ minorV L q z:=by
      obtain ⟨f,hZ,Hg⟩:= constantP A P Θ sy R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR w m 2 q Z Y' hΩQ hΔQ H ha hΓ hC; rw[Hg 0,Hg 1, Goblet.knownV]; exact tussle A P Θ sy Y U R0 L Ω Hp z Dk Uq j₀ ℓ K ε v εr Xv hB pv base Qv hp hk hR w  m Y' f hΩQ hΔQ hZ hKing q H hΓ hC hz hv h1 hHQ h0 hN hR' hY hzA t hf hpV
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.roomP
#print axioms YM.Intag.Tarot.Vista.clubs_glide
#print axioms YM.Intag.Tarot.Vista.cheersG
#print axioms YM.Intag.Tarot.Vista.testR
