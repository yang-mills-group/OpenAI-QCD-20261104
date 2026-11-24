import YM.Bloom.Gull
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
lemma cusp_lower (V:Matrix (A⊕J) (K⊕X) ℂ)(i:A): cusp V.toBlocks₁₁ i ≤ cusp V (Sum.inl i):=by
   unfold cusp; rw [Fintype.sum_sum_type]; exact le_add_of_nonneg_right (sum_nonneg (fun _ _=>norm_nonneg _))
lemma breeze1 (P Q:Matrix A J ℂ)[DecidableEq I] : (breezeP I P-breezeP I Q)=fromBlocks (P-Q) 0 0 0:=by ext i j; cases i<;>cases j <;> simp [breezeP]
include ht
lemma joining (M:Matrix (Keys f 6) (Keys c 6) ℂ)(hM:R.M=breezeP Z M): (T2).M= breezeP Z (Us*M):=by change breezeP Z Us*R.M=_; rw [hM,breezeP_comm]
include hr hp hG hw Ds he hZ
lemma dollars (i:Kx): cusp ((T2).M-(Tq).M) (Sum.inl i) ≤ pocketV Wf C' z μ D B:=by
     obtain ⟨X,Y,Z',HA,HM⟩:=ht.tilt; change R.M=breezeP Z (Buzz.wheel X Y 6) at HM; let M:=Buzz.wheel X Y 6; let K:=Q.M.toBlocks₁₁
     have hx:∀ i,cusp (M-K) i≤ z:=by
              intro i; have he:(R.M-Q.M).toBlocks₁₁ = M-K:=by rw [HM]; ext i j; rfl
              rw [← he]; exact (cusp_lower (R.M-Q.M) i).trans (hG.V₀ _ (mem_univ _))
     have hh:∀ j∈ limits (F:=6) (halo B₀ {wrap f (x i.1)}),∀ v,K j v≠0→v∈limits (halo B {o i.1}):=by
              intro j hj v hv; exact Finset.inl_mem_disjSum.mp (hr.brite i.1 (Sum.inl j) (Finset.inl_mem_disjSum.mpr hj) (Sum.inl v) hv)
     have hL: cusp (Us*M) i = cusp (splice Wf f i.2 (x i.1)*M) ():=by unfold TreeP.cusp; simp_rw [beam_aS]
     rw [joining p x w H H' F F' h g ht U M HM]; change cusp (_-breezeP Z (0:Matrix Kx (Keys c 6) ℂ)) _ ≤ _; rw [breeze1, sub_zero]; unfold TreeP.cusp; rw [Fintype.sum_sum_type]; simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,norm_zero,sum_const_zero,add_zero]; change cusp (Us*M) i ≤ _; rw [hL]; exact Buzz.taking i.2 (x i.1) Ds g F F' HA hw (o i.1) (hp _) he K hh hx hZ
lemma strap (i:Z): cusp ((T2).M-(Tq).M) (Sum.inr i)=0:=by
     obtain ⟨X,Y,Z',HA,HM⟩:=ht.tilt; change R.M=breezeP Z (Buzz.wheel X Y 6) at HM; rw [joining p x w H H' F F' h g ht U _ HM]; change cusp (breezeP Z _-breezeP Z _) _=_; rw [breeze1]; unfold TreeP.cusp; rw [Fintype.sum_sum_type]; simp
omit hr hG hZ he
include ho hx hq₂
lemma flickV (i: Yv)(hi:i∈ Id)(j:Yv)(hj:j∈Id)(hw':0<w): ‖(T2).V i j-(Tq).V i j‖ ≤ C'/w+C'*μ^2:=by
     obtain ⟨X,Y,Z',HA,HM⟩:=ht.tilt; change R.M=breezeP Z (Buzz.wheel X Y 6) at HM; let M:= Buzz.wheel X Y 6
     change ‖(T1).V i j-_‖≤_; rw [refineS p x Wf H H' F F' h g ht M HM]; let X':= Us*M; have hy:=Ds.pay; rcases i with i|i <;> rcases j with j|j <;> first| exact (show ‖(0:ℂ)-0‖ ≤ _ from by rw [sub_zero,norm_zero]; positivity)|skip -- only inl.Left
     rw [refS p Y₀ ho i hi j hj]; simp only [breezeX, Matrix.fromBlocks_apply₁₁,of_apply]
     let V:= M*Buzz.start c F' 6*M.transpose; have he: ‖(Us*V*(Us).transpose) i j‖≤ C'*μ^2:=by rw [plankS]; exact spliced i.2 j.2 Ds g F F' HA hw (x i.1) (x j.1) (hp _) (hp _) -- order x arguments
     by_cases hp':i.1=j.1
     · rw [if_pos hp',if_pos hp',zero_sub,sub_zero,norm_neg]; exact he.trans (le_add_of_nonneg_left (by positivity))
     rw [if_neg hp',if_neg hp',sub_right_comm]; apply (norm_sub_le ..).trans (add_le_add ?_ he)
     have he':=lagoon x w H H' F F' Y₀ g ht hx ho i.1 j.1 (tends p _ hi) (tends p _ hj) hp'; rw [plankS,hx]; exact hq₂.title _ (hp _) _ (hp _) i.2 j.2 _ _ F he'
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.dollars
#print axioms YM.MassiveQCD.Inky.flickV
