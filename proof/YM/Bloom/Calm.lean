import YM.Bloom.Omen
/-! # reference cross separation palette. zero self. -/
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
open YM.Bank.Jule
structure PalmT (Y:I→ E4)(T:Finset I)(ε s:ℝ) :Prop where
     pos :0<ε
     test i (h:i∈T) j (hj:j∈T) (hp:i≠j): Y i-Y j∈ Oasis ε s
variable {P:Finset I}
variable (Y₀:I→E4)(he:PalmT Y₀ P ε s)
local notation "Tq"=> stampU (Keys c 6) p Y₀
local notation "Is"=> P.biUnion (tagE p)
local notation "Id"=> P.biUnion (tagP p)
variable (hp:∀ i,p i ≤ D)
lemma owed (i: W)(h:i∈ Is): i.1 ∈ P:=by obtain ⟨j,hj,h⟩:= mem_biUnion.mp h; rw [(mem_filter.mp h).2]; exact hj
lemma tends (i: Kx)(h:Sum.inl i∈Id): i.1 ∈ P:=by obtain ⟨j,hj,h⟩:=mem_biUnion.mp h; rw [show i.1=j from (mem_filter.mp h).2]; exact hj
include he
lemma refG (i:W)(hi:i∈ Is)(j:W)(hj:j∈ Is) : (Tq).Q.cov i j= if i.1=j.1 then 0 else viewK i.2 j.2 (Y₀ i.1-Y₀ j.1) :=by
     change (if Y₀ i.1=Y₀ j.1 then 0 else viewK i.2 j.2 (Y₀ i.1-Y₀ j.1)) = _ -- syntax viewK
     by_cases hp:i.1=j.1; · simp [hp]
     rw [if_neg (sub_ne_zero.mp (door (he.test _ (owed p i hi) _ (owed p j hj) hp) he.pos)),if_neg hp]
lemma refS (i:Kx)(hi:Sum.inl i∈ Id)(j:Kx)(hj:Sum.inl j∈ Id): (Tq).V (Sum.inl i) (Sum.inl j)= if i.1=j.1 then 0 else QCD.Bloom.pin i.2 j.2 (Y₀ i.1) (Y₀ j.1):=by
     change Arise.Count.callS Y₀ p i j=_; unfold callS; rw [Matrix.of_apply]; by_cases hp:i.1=j.1; · rw [if_pos hp, if_pos (congr_arg _ hp)] -- order
     rw [if_neg (sub_ne_zero.mp (door (he.test _ (tends p i hi) _ (tends p j hj) hp) he.pos)),if_neg hp]; rcases i with ⟨i,x|x⟩ <;> rcases j with ⟨j,y|y⟩ <;> simp [QCD.Bloom.pin,QCD.Bloom.chief,QCD.Bloom.coreW]
include Dg Ds hp
lemma ref_budget (c:Side)(ht:1 ≤ Ξ)(hc:C≤Ξ)(hC:C'≤ Ξ): Sky (stampU (Keys c 6) p Y₀).P (stampU (Keys c 6) p Y₀).Q (stampU (Keys c 6) p Y₀).M (stampU (Keys c 6) p Y₀).V (P.biUnion (tagE p)) (P.biUnion (tagP p)) Ξ Ξ Ξ Ξ :=by
     have h0:= zero_le_one.trans ht; let T:= stampU (Keys c 6) p Y₀
     refine ⟨ht,h0,ht,h0,fun i hi=>?_,fun i hi j hj=>?_,?_,?_⟩
     · change ∑ _j:Unit,‖(0:ℂ)‖ ≤ Ξ; simpa using h0
     · rw [refG p Y₀ he i hi j hj]; split; · simpa using h0
       next hz=> exact (Dg.sense _ (hp _) _ (hp _) _ _ _ (he.test _ (owed p _ hi) _ (owed p _ hj) hz)).trans hc
     · intro i hi; cases i with
       | inl a=>change cusp (breezeP Z (0:Matrix Kx (Keys c 6) ℂ)) (Sum.inl a) ≤ _; rw [rows_breeze]; simpa only [TreeP.cusp,Matrix.zero_apply, norm_zero,sum_const_zero] using h0
       | inr a=>change cusp (breezeP Z (0:Matrix Kx (Keys c 6) ℂ)) (Sum.inr a) ≤ _; rw [ticks_breeze]; exact ht
     rintro (i|i) hi (j|j) hj <;> first| exact (show ‖(0:ℂ)‖ ≤ Ξ by simpa using h0)|skip
     rw [refS p Y₀ he i hi j hj]; split; · simpa using h0
     next he'=> rw [pin_ch]; exact (Ds.sense _ (hp _) _ (hp _) _ _ _ (he.test _ (tends p _ hi) _ (tends p _ hj) he')).trans hC
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.ref_budget
