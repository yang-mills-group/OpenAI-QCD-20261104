import YM.Bloom.Calm
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
include ht
private lemma matrix_p : ∃ (J:Matrix (Body 2 f) (Body 2 c) ℝ), R.P=chalk c f J∧ ∃ V W', YM.Bank.TowerW k g H H' J V W' :=by obtain ⟨J,V,W',hx,h⟩:=ht.hue; exact ⟨_,h,_,_,hx⟩
lemma beam_path0 (i:W) : (T2).P i ()=(pots Wf f i.2 (x i.1)*R.P*jetO su c ξ U) () ():=by
     let V:= TimesV.linearV ξ U; have he:(T2).P= Ug*R.P*(jetO su c ξ U):= rfl
     rw [he,Matrix.mul_apply]; conv_rhs=>rw [Matrix.mul_apply]
     simp_rw [beam_aG]
include hG hq hU hA hr Dg hp hP hP' hv he hZ
lemma plateP (i:W): cusp (T2).P i ≤ X₂*(crop su Wf C z μ D B*X₁):=by
    obtain ⟨J,hW,h'⟩:= matrix_p H H' F F' g ht
    have hx := Dg; have hs:∀ i,cusp (chalk c f J-Q.P) i ≤ z:= fun i=>hW ▸ hG.G₀ i (mem_univ i) -- test
    have hh : Fare k a b g J H H' := highG H H' g J h' hP hP' hv
    have ht':= lightU Dg U i.2 (x i.1) H H' g J hh (hp _) hq he x i.1 o rfl hr hs hZ hU hA; unfold TreeP.cusp at ht' ⊢; simp only [Fintype.sum_unique, Subsingleton.elim (default:Unit) ()] at ht' ⊢; rw [beam_path0 p x w H H' F F' h g ht U i,hW]; exact ht'
omit hG hq hU hA hr Dg hp hP hP' hv he hZ
variable (hx:Y₀=posT w (2*n)∘x)(ho:PalmT Y₀ P ε s) -- I→ E4
include hx ho
lemma lagoon (i j:I)(hi:i∈P)(hj:j∈P)(hp:i≠j) : posT w (2*n) (x i-x j)∈Oasis ε s:=by rw [unspread]; rw [hx] at ho; exact ho.test i hi j hj hp -- uses ht inadvertently omit!
variable (hq₁: Acquired su D n a v b ε s C w f)(hq₂:Tropic D n j ε s C' w f)
include Dg hq₁ hP hP' hv hp hq
lemma waveP (i:W)(hi:i∈ Is)(j:W)(hj:j∈ Is)(hx':0< w): ‖(T2).Q.cov i j-(Tq).Q.cov i j‖ ≤ C/w+C*μ^2:=by
     obtain ⟨J,hW,h'⟩:= matrix_p H H' F F' g ht; have hh : Fare k a b g J H H':= highG H H' g J h' hP hP' hv
     let V:=R.P*chalkW c H'*R.P.transpose
     have he: ‖(Ug*V*(Ug).transpose) i j‖ ≤ C*μ^2:= by unfold V; rw [plankG,hW]; exact lowU Dg i.2 j.2 (x i.1) (x j.1) H H' g J hh (hp _) (hp _) hq -- edit
     change ‖(T1).Q.cov i j-_‖ ≤ _; rw [refG p Y₀ ho i hi j hj, refineG p x (w^n) H H' F F' h g ht i j]
     by_cases hp':i.1=j.1
     · rw [if_pos hp',if_pos hp',zero_sub,sub_zero,norm_neg]; exact he.trans (le_add_of_nonneg_left (div_nonneg Dg.pay.le hx'.le))
     rw [if_neg hp', if_neg hp']; let U:= Ug*chalkW f H*(Ug).transpose; let X:=viewK i.2 j.2 (Y₀ i.1-Y₀ j.1); change ‖U i j-(Ug*V*(Ug).transpose) i j-X‖≤ _; rw [sub_right_comm]; apply (norm_sub_le ..).trans (add_le_add ?_ he)
     have he':=lagoon x w H H' F F' Y₀ g ht hx ho i.1 j.1 (owed p _ hi) (owed p _ hj) hp'; unfold U X; rw [plankG,hx]; exact (show _ from by simp only [Function.comp_apply, ←unspread]; exact view_read i.2 j.2 _ _ H hq₁ (hp _) (hp _) hP he') -- edit
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.plateP
#print axioms YM.MassiveQCD.Inky.waveP
