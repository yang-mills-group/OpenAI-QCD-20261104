import YM.Bloom.Gorge
/-! # Crew actual budget input post.Weights. Native Gauge.M. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Inky
open QCD QCD.Lat Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory
open Precision Exterior Bloch Laurent
open QCD.Creek QCD.Cove QCD.Flume QCD.Free YM.Next.Free
open YM.Arise YM.Arise.Count YM.Bloom YM.Bloom.TreeP YM.Bloom.Jar
open Ribbon Cape Play Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit
open Rebus Matrix Vest TimesV Arise.Bill Arise.Range
open QCD.Bloom QCD.Bloom.Buzz YM.Next.Rank.Normal Massive.UV Arise.Parcel
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{A J K X Y I:Type}[Fintype A][Fintype J][Fintype K][Fintype X][Fintype Y][Fintype I]
variable {k d i j m n B L B₀ t' D q:ℕ} {Q R:Tone (Kh f) (Dh f 6 I) (Kh c) (Dh c 6 I)}
variable {a b v y' ε s C C' μ θ ξ ν z X₁ X₂ Ξ:ℝ}
variable (Dg:Eyes su D L (2*n) k a v b ε s C) (Ds:Spar D L (2*n) j ε s C')
-- Loom. goals.Ne
variable (p:I→ℕ)(x:I→ Cover)(w:ℝ) (H H':Bed)(F F':Train j)(h:(chalkW f H).IsSymm)
local notation "Wf"=> w^n
local notation "Tπ"=> shone p x (w^n) f H F h
local notation "Kx"=> Arms p
local notation "W"=> (Svg p)
local notation "Ug"=> beamG p x (w^n) f
local notation "Us"=> beamL p x (w^n) f
local notation "Yv"=> Tv p
local notation "Z"=> Spine I
open YM.Bank.Jule
variable {P: Finset I} (Y₀:I→ E4)
local notation "Tq"=> stampU (Keys c 6) p Y₀
local notation "Is"=> P.biUnion (tagE p)
local notation "Id"=> P.biUnion (tagP p)
variable (g:Ratio c f)(ht:Canon k j H H' F F' R g)(o:I→ Site c)
variable (hr:Vision ((wrap f) ∘ x) o B₀ B Q)
variable (hp:∀ i,p i ≤ D)(he:L≤ B₀)(hG:R.Gale Q z)(hZ:0 ≤ z)
-- given.Y actual
variable (hP: Grain a v b H f)(hP': Grain a v b H' c)(hv:0<v)
variable (hq:Factor (w^n) D g.count μ)(hw: Porter (w^n) D g.count μ)
variable (U: Directions su c)(hU:‖U‖ ≤ X₁)(hA:|ξ⁻¹|≤ X₂)
-- Post.F
local notation "T1"=> Tone.after (shone p x (w^n) f H F h) R
local notation "T2"=>frost (Tone.after (shone p x (w^n) f H F h) R) (TimesV.linearV ξ U)
variable (hx:Y₀=posT w (2*n)∘x)(ho:PalmT Y₀ P ε s)(hq₁:Acquired su D n a v b ε s C w f)(hq₂:Tropic D n j ε s C' w f)
lemma constrainP (f q:Tone A X J Y) (S:Finset A)(T: Finset X) (hv:Sky q.P q.Q q.M q.V S T s s s s)(hp:drifts f.P f.Q f.M f.V q.P q.Q q.M q.V S T a)(ha:0 ≤ a): Sky f.P f.Q f.M f.V S T (s+a) (s+a) (s+a) (s+a):=by
    have hh:=hv.craze; have ht:=hh.trans (le_add_of_nonneg_right ha); have hx:=zero_le_one.trans ht
    have hQ {K X:Type}[Fintype K][Fintype X](P R:Matrix K X ℂ)(S:Finset K)(hp:QCD.Anomaly.bills (P-R) S a)(hq:QCD.Anomaly.bills R S s): QCD.Anomaly.bills P S (s+a):=by
          intro i hi; change TreeP.cusp P i ≤ _; rw [show P= R+(P-R) from by abel]; exact (TreeP.cups_add R _ _).trans (add_le_add (hq i hi) (hp i hi))
    refine ⟨ht,hx,ht,hx,hQ _ _ _ hp.G₀ hv.gu,fun i hi j hj=>?_, hQ _ _ _ hp.V₀ hv.po,fun i hi j hj=>?_⟩
    · have hz:= hp.G₁ i hi j hj; change ‖f.Q.cov i j + - q.Q.cov i j‖ ≤ a at hz; rw [←sub_eq_add_neg] at hz; calc
           _ ≤ ‖f.Q.cov i j-q.Q.cov i j‖+‖q.Q.cov i j‖:= norm_le_norm_sub_add ..
           _ ≤ _ := (add_le_add hz (hv.sec i hi j hj)).trans_eq (add_comm ..)
    calc
       _ ≤ ‖f.V i j-q.V i j‖+‖q.V i j‖:= norm_le_norm_sub_add ..
       _ ≤ _:= (add_le_add (hp.V₁ i hi j hj) (hv.trib i hi j hj)).trans_eq (add_comm ..)
include Dg Ds hx ho hr hP hP' hv hU hA hp hG hZ hq hw he ht hq₁ hq₂
variable {Z':ℝ} (ht₁:0<w)(hz':0 ≤ Z') (hC:X₂ * (TreeP.crop su (w^n) C z μ D B*X₁) ≤ Z') -- notation Wf in binder risk use explicit
variable (hL: pocketV (w^n) C' z μ D B ≤ Z')(hC':C/w+C*μ^2 ≤ Z')(hL': C'/w+C'*μ^2≤ Z')
include ht₁ hz' hC hL hC' hL'
lemma reserves : drifts (T2).P (T2).Q (T2).M (T2).V (Tq).P (Tq).Q (Tq).M (Tq).V Is Id Z':=by
     refine ⟨fun i hi=>?_,fun i hi j hj=>?_,?_,fun i hi j hj=>?_⟩
     · change cusp ((T2).P-0) i≤_; rw[sub_zero]; exact (plateP Dg p x w H H' F F' h g ht o hr hp he hG hZ hP hP' hv hq U hU hA i).trans hC
     · change ‖(T2).Q.cov i j+ - (Tq).Q.cov i j‖≤ _; rw [← sub_eq_add_neg]; exact (waveP Dg p x w H H' F F' h Y₀ g ht hp hP hP' hv hq U hx ho hq₁ i hi j hj ht₁).trans hC'
     · rintro (i|i) hi; · exact (dollars Ds p x w H H' F F' h Y₀ g ht o hr hp he hG hZ hw U i).trans hL
       exact (strap Ds p x w H H' F F' h Y₀ g ht o hr hp he hG hZ hw U i).trans_le hz'
     exact (flickV Ds p x w H H' F F' h Y₀ g ht hp hw U hx ho hq₂ i hi j hj ht₁).trans hL'
local notation "S!" f:arg z:arg=> Sky (Tone.P f) (Tone.Q f) (Tone.M f) (Tone.V f) Is Id z z z z -- maybe
variable (Δ:ℝ)(hΔ:1 ≤ Δ)(hz₀: C ≤ Δ)(hz₁:C'≤ Δ)
include hΔ hz₀ hz₁
lemma scarcity : (S! T2 (Δ+Z')) ∧ (S! Tq (Δ+Z')):=by
     have hℓ:=ref_budget Dg Ds p Y₀ ho hp c hΔ hz₀ hz₁; let v:=Δ+Z'; have hx': Δ≤v:= le_add_of_nonneg_right hz'; have hh:= reserves Dg Ds p x w H H' F F' h Y₀ g ht o hr hp he hG hZ hP hP' hv hq hw U hU hA hx ho hq₁ hq₂ ht₁ hz' hC hL hC' hL'
     have ht:1 ≤ v:= hΔ.trans hx'; have hv:=zero_le_one.trans ht; exact ⟨constrainP T2 Tq Is Id hℓ hh hz',⟨ht,hv,ht,hv,fun i hi=> (hℓ.gu i hi).trans hx',fun i hi j hj=>(hℓ.sec i hi j hj).trans hx',fun i hi=> (hℓ.po i hi).trans hx',fun i hi j hj=> (hℓ.trib i hi j hj).trans hx'⟩⟩
open FlareV
-- ultimate cap recipe.Payment.
variable (qᵢ:I→Bool)(P'P:I→ Papers (Svg p) (Patio (Tv p)))(b':ℕ)(b₁ b₂ b₃:ℕ) (hm₀:∀ i∈P,P'P i∈ Ledger (tagP p i) (tagE p i) b₁ b₂)
variable (hb:P.card ≤ b')(hwv:I→ℝ)(he₀:∀ i∈P,cents (P'P i) ≤ Ξ)(he₁: 1 ≤ Ξ)
include hm₀ hb he₀ he₁
lemma cherubs (U₀:I→ℝ)(V:Finset I)(hV:V ⊆P) :
     let U' : Finset I→ Papers (Kh f) (Patio (Dh f 6 I)):= Arise.Count.pivotV (shone p x (w^n) f H F h) P'P hwv; let K:= cetacea (Arise.Count.pence (stampU (Keys c 6) p Y₀) P'P) V; let Ω:= Play.Chamber.switch U' R.P R.Q R.M R.V V; ‖ give U₀ V • Oce.rose (Dh c 6 I) (TimesV.linearV ξ U) Ω-give (U₀*hwv) V • K‖≤ ‖give (U₀*hwv) V‖*(Arise.Count.corona (Δ+Z') Ξ b₁ b₂ b'*Z'):=by
      intro U' K Ω; unfold Ω U'; rw [Arise.Count.earnsV Tπ R P'P hwv (tagP p) (tagE p) hm₀ (fun i _ j _ he=> freshTag p x Wf H F h i j he) U₀ (TimesV.linearV ξ U) V hV,← _root_.smul_sub,norm_smul]
      have hg:= scarcity Dg Ds p x w H H' F F' h Y₀ g ht o hr hp he hG hZ hP hP' hv hq hw U hU hA hx ho hq₁ hq₂ ht₁ hz' hC hL hC' hL' Δ hΔ hz₀ hz₁
      have hh:= reserves Dg Ds p x w H H' F F' h Y₀ g ht o hr hp he hG hZ hP hP' hv hq hw U hU hA hx ho hq₁ hq₂ ht₁ hz' hC hL hC' hL'
      let e:Finset (Svg p):=@Finset.biUnion _ _ (fun a b=>Classical.propDecidable (a=b)) P (tagE p); let z:Finset (Tv p):=@Finset.biUnion _ _ (fun a b=> Classical.propDecidable (a=b)) P (tagP p); have h1:Is=e:=by unfold e; congr; exact Subsingleton.elim ..
      have h2:Id=z:=by unfold z; congr
      rw [h1,h2] at hg hh
      exact mul_le_mul_of_nonneg_left (Arise.Count.compensation P'P (tagP p) (tagE p) hm₀ hb hg.1 he₀ he₁ hg.2 hz' hh V hV) (norm_nonneg _)
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.reserves
#print axioms YM.MassiveQCD.Inky.cherubs
