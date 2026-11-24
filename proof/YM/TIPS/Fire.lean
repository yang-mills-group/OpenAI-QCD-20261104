import YM.TIPS.Outlook
import YM.Eden.Pale
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
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
variable {c f:Side}{A J K X Y I:Type}[Fintype A][Fintype J][Fintype K][Fintype X][Fintype Y][Fintype I]
variable {k d i j m n B L B₀ t' D q:ℕ}
variable {a b v y' ε s C C' μ θ ξ ν z X₁ X₂ Ξ:ℝ}
variable (p:I→ℕ)(x:I→ Cover)(w:ℝ) (H:Bed)(F:Train j)(h:(chalkW f H).IsSymm)
-- vertices of legit ship.I.rim bound all.Estim physical stance. ATTEMPT with high caps ≥card(Pairs) etc. 
open YM.Eden MassiveQCD.Sample MassiveQCD.Sample.Taxing QCD.Anomaly QCD.Grass
-- Rim pol bound whatever p0.Pr. <dim S.
local notation "Kx"=> Keys f 6
set_option maxHeartbeats 800000 in
lemma glib (a:I→Bool)(i:I)(b:ℝ)(P':Bard d)(U:Grid f): Ribbon.stake Kx (burst a {i}) (wide d b P' f (x i) U)∈ QCD.Anomaly.Rim univ (Fintype.card (Pairs (SpinMode d))+6):=by
   rw [wow]; induction P' using TensorProduct.induction_on with
   | zero=> rw [map_zero,map_zero]; exact Submodule.zero_mem _
   | add P Q hp hQ=> rw [map_add,map_add]; exact Submodule.add_mem _ hp hQ
   | tmul P Q=>
        rw [power_t,map_smul]; apply Submodule.smul_mem; let V:= rateS d (x i) U Q; have hV: V∈ QCD.Anomaly.Rim univ (Fintype.card (Pairs (SpinMode d))):= QCD.Anomaly.Rim.patched (QCD.Eden.mood d (x i) U) (fun i _ j _=>mem_univ _) (U:=univ) (show Q∈ QCD.Anomaly.Rim _ _ from (fun i _=> ⟨subset_univ _, card_le_univ i⟩))
        let Z:=Ribbon.burst a {i}; let Y:=Ribbon.Spine I; rw [Ribbon.markedOut]; apply QCD.Anomaly.Rim.multiply
        · let y:=univ.filter fun i:Finset (Keys f 6)=>True; let g: Kx ↪ (Kx ⊕ Y):=Embedding.inl; change embed g V∈ _; rw [QCD.Anomaly.Rim.record hV, map_sum]; refine Submodule.sum_mem _ (fun i hi=>?_); have hv: i.card≤ _:= (mem_filter.mp hi).2; rw [map_smul]; apply Submodule.smul_mem; rcases embed_blade g i with h|h<;>rw [h]; exact QCD.Anomaly.Rim.layerIn (subset_univ _) (by simpa using hv); exact Submodule.neg_mem _ (QCD.Anomaly.Rim.layerIn (subset_univ _) (by simpa using hv))
        let f:Y↪(Kx⊕Y):=Embedding.inr; have hx: (Z.map f).card≤ 6:=by rw [Finset.card_map]; unfold Z; rw [onePost]; split<;>omega
        change embed f _∈ _; have hm:=QCD.Anomaly.Rim.layerIn (subset_univ (Z.map f)) hx; rcases embed_blade f Z with h|h<;>rw [h]; exact hm; exact Submodule.neg_mem _ hm
variable (JX:∀ i:I,Label (p i)) (a₁ s₁ t₁:I→ℕ) (hQ:∀ i:I,((milky 0 H f (G:=su) (d':=p i))).IsSymm)
variable (u:I→ℝ) (η:ℝ)
noncomputable def staff (i:I): Insertion f 6:= (u i:ℂ) • lotus (p i) H f F (hQ i) w η (JX i).val f (x i)
open Massive.Evo Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
variable (Vb:BudgetPoint)(hm:∀ i:I,(JX i).val ∈ Rtg (p i) (a₁ i) (s₁ i) (t₁ i))
set_option quotPrecheck false
local notation "qᵀ"=> fun i:I=> polarity (t₁ i)
local notation "o"=> (wrap f∘x)
local notation "B✶"=> Vb.B
local notation "F✶"=> staff p x w H F JX hQ u η
local notation "Ten" i:arg=>Massive.Evo.Ten (a₁ i) (s₁ i) (t₁ i) w η Vb.threshold v
local notation "G✶" i:arg=> Zodiac (p i) (a₁ i) (s₁ i) (t₁ i) w η Vb.threshold v H f F (hQ i) (JX i)
variable (hj: 2 ≤ j)(hw:0<w)(ht:0<η)(hU:0<v)
open Massive.Poised Massive.Poised.Plans
include hw ht hU
lemma invested (i:I): F✶ i= ((u i:ℂ)*(Ten i:ℂ)) • ((G✶ i) f (x i)):=by
   have hx :0<Ten i:= dollar0 (a₁ i) (s₁ i) (t₁ i) hw ht Vb.threshold_pos hU
   let L:=lotus (p i) H f F (hQ i) w η (JX i).val; let t:=Ten i; unfold Zodiac doll; change (u i:ℂ) • L f (x i)= ((u i:ℂ)*(t:ℂ)) • ((↑t:ℂ)⁻¹ • L f (x i)); rw [mul_smul,smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hx.ne')]
include hm hj Vb
lemma loans : ∀ (i:I)(V:Grid f),Grass.Hom (polarity (t₁ i)) ((F✶ i) V):=by intro i V; rw [invested (v:=v) p x w H F JX a₁ s₁ t₁ hQ u η Vb hw ht hU]; exact (polarE (JX i) (hm i) w η F hj _ V).smul _ -- include v not in statement.
local notation "hκ"=> loans (v:=v) p x w H F JX a₁ s₁ t₁ hQ u η Vb hm hj hw ht hU
variable (lℓ mℓ:ℕ)
lemma script (hv:∀ i:I,Fintype.card (Pairs (SpinMode (p i)))+6 ≤ mℓ)(hh:True):∀ i V, ((shipY o qᵀ Vb (fun i:I=>(F✶ i : Grid f→ Lat.Fields f 6)) hκ lℓ).mark i V).val∈ QCD.Anomaly.Rim univ mℓ:=by
     intro i V; change Ribbon.stake Kx _ ((u i:ℂ) • _ )∈ _; rw [map_smul]; refine Submodule.smul_mem _ _ (Rim.monotone (Subset.refl _) (hv i) (show _ from glib (d:=p i) x qᵀ i η (reelW (p i) H f F (hQ i) (padU (p i) w (introduce (p i) (JX i).val))) V)) -- adjust hℓ
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.script
