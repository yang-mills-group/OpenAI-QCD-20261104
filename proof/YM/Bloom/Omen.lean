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
lemma freshTag (i j:I)(hv:i≠j): Disjoint (tagP p i) (tagP p j) ∧ (∀ a∈tagP p i,∀ b∈tagP p j,(Tπ).V a b=0)∧∀ a∈tagE p i,∀ b∈tagE p j,(Tπ).Q.cov a b=0:=by
     refine ⟨disjoint_left.mpr (fun v h h'=>hv (((mem_filter.mp h).2).symm.trans (mem_filter.mp h').2)),?_,?_⟩
     · intro a ha b hb; rcases a with a|a <;> rcases b with b|b <;> first|rfl|skip
       exact if_neg (fun h=> hv (((mem_filter.mp ha).2).symm.trans ((show occupant p _=occupant p _ from h).trans (mem_filter.mp hb).2)))
     intro a ha b hb; exact if_neg fun h=> hv (((mem_filter.mp ha).2).symm.trans (h.trans (mem_filter.mp hb).2))
lemma rows_breeze (M :Matrix A J ℂ)[DecidableEq I](i:A): cusp (breezeP I M) (Sum.inl i)=cusp M i:=by unfold cusp breezeP; rw [Fintype.sum_sum_type]; simp
lemma ticks_breeze (M :Matrix A J ℂ)[DecidableEq I](i:I): cusp (breezeP I M) (Sum.inr i)=1:=by unfold cusp breezeP; rw [Fintype.sum_sum_type]; simp [Matrix.one_apply,apply_ite (fun x:ℂ=>‖x‖)]
variable (hp:∀ i, p i≤ D)
include Dg Ds hp
lemma deserve (ht:1≤ w)(hv:Grain a v b H f) (hx:1 ≤ Ξ)(hA:billN w D*(billN w D*C) ≤ Ξ)(hB: billN w D*(billN w D*C')≤ Ξ) : Tone.Rich (Tπ) Ξ:=by
     have hz:= zero_le_one.trans hx; have hg := Dg.pay; have hu:=Ds.pay; have he:1≤ billN w D:=one_le_pow₀ ht; have hd:0 < billN w D:=zero_lt_one.trans_le he
     refine ⟨hx,hz,hx,hz,?_,?_,?_,?_⟩
     · intro i _; change cusp (Ug) i ≤ _; exact (wears i.2 (x i.1) Dg (hp _) ht).trans ((le_mul_of_one_le_left (mul_nonneg hd.le hg.le) he).trans hA)
       -- edit
     · intro i _ j _; rw [sloganP]; split_ifs; swap; · simpa using hz
       rw [norm_neg,plankG]; exact (priceG i.2 j.2 (x i.1) (x j.1) H Dg (hp _) (hp _) hv ht).trans hA
     · rintro (i|i) _
       · change cusp (breezeP Z Us) (Sum.inl i) ≤ _; rw [rows_breeze]; exact (Buzz.packed (c:=f) i.2 (x i.1) Ds ht (hp i.1)).trans ((le_mul_of_one_le_left (mul_nonneg hd.le hu.le) he).trans hB)
       change cusp (breezeP Z Us) (Sum.inr i) ≤ _; rw [ticks_breeze]; exact hx
     rintro (i|i) _ (j|j) _ <;> first| exact (show ‖(0:ℂ)‖ ≤ Ξ from by simpa using hz)|skip
     rw [sloganS]; split; swap; · simpa using hz
     rw [norm_neg,plankS]; exact (Buzz.settled i.2 j.2 (x i.1) (x j.1) Ds F (hp i.1) (hp j.1) ht).trans hB
-- scope maps prices from plates
lemma appear (i:I)(z:W)(hz:z∈tagE p i)(a:Kh f)(ha:(Tπ).P z a≠0)(hs:L≤ B):a∈can ((wrap f)∘x) B i:=by
     have he:= (mem_filter.mp hz).2; rw [← he,portionU]; exact liteU z.2 (x z.1) Dg (hp _) hs _ ha
lemma appears (i:I)(z:Yv)(hz:z∈tagP p i)(a:Dh f 6 I)(ha:(Tπ).M z a ≠0) (hs:L≤ B):a∈spineP ((wrap f)∘x) 6 B i:=by
     have he: occupant p z=i:= (mem_filter.mp hz).2; rcases z with z|z <;> rcases a with a|a
     · apply inl_mem_disjSum.mpr; rw [← he]; exact locked z.2 (x z.1) Ds (hp _) hs a ha
     · exact (ha rfl).elim
     · exact (ha rfl).elim
     have hA: a=z:=by by_contra hc; exact ha (Matrix.one_apply_ne (Ne.symm hc))
     apply inr_mem_disjSum.mpr; rw [hA]; exact mem_filter.mpr ⟨mem_univ z,he⟩
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.deserve
#print axioms YM.MassiveQCD.Inky.appears
