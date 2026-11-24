import YM.TIPS.Hone
import YM.Eden.Pale
import YM.Bloom.Boot
/-! # Estimate post.MW. auxiliary top ledger uniform.ALL.Arity. -/
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
variable (p:I→ℕ)(x:I→ Cover)(w:ℝ) (H:Bed)(F:Train j)(h:(chalkW f H).IsSymm)
local notation "Tπ"=> shone p x w f H F h
local notation "Kx"=> Arms p
local notation "W"=> (Svg p)
local notation "Ug"=> beamG p x w f
local notation "Us"=> beamL p x w f
local notation "Yv"=> Tv p
local notation "Z"=> Spine I
variable (q:I→Bool)(P:∀ i,Cups (p i) (q i))(T:Finset (Finset I))(b:I→ℝ) -- b shadows Dg.b; rename
open Sample.Taxing Sample.Quills QCD.Kit
variable (G:I→ Grid f→QCD.Lat.Fields f 6) (hP:∀ (i:I)(U:Grid f), Grass.Hom (q i) (G i U))
set_option quotPrecheck false
local notation "z!"=>wrap f ∘ x
local notation "Vp"=>fun i:I=> port q p i (P i)
local notation "P₀"=>Arise.Count.pivotV Tπ Vp b
variable (B' : BudgetPoint)(u r₀ κ τ ε₁:ℝ)(l t:ℕ) -- remove notation.P.Grades k0
variable (hp:∀ i,p i≤D)
include Dg Ds hp
local notation "ZK"=> shipY z! q B' G hP l
variable (k0:ℕ)(hL:∀ i, port q p i (P i) ∈ Ledger (tagP p i) (tagE p i) k0 t)
include hL
lemma horizonQ (hs:L≤ majorT l*B'.B)(hH:Tone.Rich (shone p x w f H F h) X₁)
    (hV:∀ i:I, |b i| * (emmet X₁ X₁ X₁ X₁ k0 t*cents (port q p i (P i))) ≤ τ)
    (he:0 ≤ ε₁) (ht:0 ≤ τ)
    (hY:∀ (i:I)(U:Directions su f),{i}∈T→ ‖U‖ ≤ r₀→ Healthy B'.threshold (cups (wrap f ∘ x) (innerT l*B'.B) {i}) (increment 1 U)→ ‖Ribbon.stake (Keys f 6) (burst q {i}) (G i (increment 1 U))- (Oce.rose (Dh f 6 I) (karm κ (increment 1 U)) ((b i:ℂ) • (Tπ).read ((Vp) i))).val‖ ≤ ε₁) : Moor z! T ZK Finset.univ P₀ B'.B l k0 t B'.threshold r₀ κ τ ε₁:=by
    have hg(i:I) : P₀ {i}= (b i:ℂ) • (Tπ).read ((Vp) i):=Arise.Count.milk1 ..
    have hQ (j:Finset I)(he:j.card≠1): P₀ j=0:=dif_neg he
    have hy(i:I) : (Tπ).read ((Vp) i)∈Ledger (spineP z! 6 (majorT l*B'.B) i) (can z! (majorT l*B'.B) i) k0 t:=QCD.Bera.types _ _ _ _ (hL i) (fun a ha j hh=> appear Dg Ds p x w H F h hp i a ha j hh hs) (fun a ha j hh=> appears Dg Ds p x w H F h hp i a ha j hh hs)
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · intro i hi hv; by_cases he:i.card=1
      · obtain ⟨i,rfl⟩:= card_eq_one.mp he; rw [hg]; apply Submodule.smul_mem; simpa only [Finset.singleton_biUnion,card_singleton,one_mul] using hy i -- deqid.
      rw [hQ i he]; exact Submodule.zero_mem _
    · intro i hi hv hk; have ht:i.card=1:=Classical.byContradiction fun h=>hk (hQ i h); obtain ⟨j,rfl⟩:=card_eq_one.mp ht; exact ⟨singleton_nonempty _,fun a ha b hb=> (((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm) ▸ Relation.ReflTransGen.refl)⟩
    · intro i hi hv; by_cases he:i.card=1
      · obtain ⟨i,rfl⟩:= card_eq_one.mp he; have hp':=QCD.Bera.tolled (Tπ).P _ _ _ ((Vp) i) (leaguer (hL i) (subset_univ _) (subset_univ _) le_rfl le_rfl) hH; rw [hg,smul_cent,Complex.norm_real,Real.norm_eq_abs,card_singleton,pow_one]; exact (mul_le_mul_of_nonneg_left hp' (abs_nonneg _)).trans (hV i)
      rw [hQ i he]; exact (show cents (0:Papers (Kh f) (Patio (Dh f 6 I)))=0 from by simp).trans_le (pow_nonneg ht _)
    intro i hi hv V hV hv'; by_cases h₁:i.card=1
    · obtain ⟨p,rfl⟩:=card_eq_one.mp h₁
      rw [show sled ZK univ _ (increment 1 V)=_ from (show sled ZK univ {p} (increment 1 V)=(ZK).mark p (increment 1 V) from ?_),hg]; exact hY p V hi hV hv'
      unfold sled; rw [Finset.sum_filter, sum_eq_single p,if_pos (show (ZK).z p={p} from rfl)]; intro j hj hJ; exact if_neg (fun h=>hJ (singleton_injective h)); simp
    rw [show sled ZK _ i _=0 from ?_, hQ i h₁,map_zero,sub_zero,norm_zero]; exact he
    unfold sled; rw [Finset.sum_filter]; exact sum_eq_zero (fun j _=>if_neg (fun h=> h₁ ((show {j}=i from h) ▸ card_singleton j))) -- orientation
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.horizonQ
