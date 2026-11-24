import YM.Bloom.Glyph
import YM.Vest.Pair
import YM.Arise.Parcel
/-! # adapt budgets LoomT Inst; compose Cmd.In.St.Seams. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Inky
open QCD QCD.Lat Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory
open Precision Exterior Bloch Laurent
open QCD.Creek QCD.Cove QCD.Flume QCD.Free YM.Next.Free
open YM.Arise YM.Arise.Count YM.Bloom YM.Bloom.TreeP
open Ribbon Cape Play Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit
open Rebus Matrix Vest TimesV
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{A J K X Y I:Type}[Fintype A][Fintype J][Fintype K][Fintype X][Fintype Y][Fintype I]
variable {k d i j m n B L B₀ t' D q:ℕ} {Q R:Tone (Kh f) (Dh f 6 I) (Kh c) (Dh c 6 I)}
variable {a b v y' ε s C w μ θ ξ ν z X₁ X₂:ℝ}
variable (Dg:Eyes su D L (2*n) j a v b ε s C)
-- try lemma definally Eq.G
variable (U:Directions su c)(p:Zinc su k)(p':Zinc su d)(x y: Cover)
structure Vision (o:I→ Site f) (w:I→ Site c) (B₀ B:ℕ)(Q: Tone (Kh f) (Dh f 6 I) (Kh c) (Dh c 6 I)):Prop where
    watch : ∀ i (p:Kh f),p∈ can o B₀ i →∀ q, Q.P p q ≠0→ q∈can w B i
    brite : ∀ i (p:Dh f 6 I),p∈ spineP o 6 B₀ i→∀ q,Q.M p q ≠0→ q∈ spineP w 6 B i
lemma portionU (o:I→ Site c) (p:Kh c)(i:I) : p ∈ can o B i ↔ p∈ YM.Bloom.TreeP.clique su c 2 B (o i):=by rw [TreeP.clique_ion]; simp [can]
include Dg
-- Transport (Try). lemma assuming parent Fare with genuine. Use pay type inequality adapt
variable (R₀ R₁:Bed)(g: Ratio c f)(M: Matrix (Exterior.Body 2 f) (Exterior.Body 2 c) ℝ) (hp: YM.Bloom.Fare j a b g M R₀ R₁)
local notation "wP"=> pots w f p x
local notation "sP"=> pots w f p' y
local notation "Cp"=> chalk c f M
include hp
lemma lightU (hk:k ≤ D)(hq:Factor w D g.count μ)(hs:L ≤ B₀)(o:I→ Cover)(i:I) (u:I→Site c) (he:x=o i)(hR:Vision ((wrap f)∘o) u B₀ B Q)(ht:∀ i,cusp (Cp-Q.P) i≤ ν)(hy:0 ≤ ν)(hU:‖U‖ ≤ X₁)(hz:|ξ⁻¹|≤ X₂): cusp (wP*Cp*jetO su c ξ U) ()≤ X₂*(crop su w C ν μ D B*X₁):=by
    apply jump inferInstance inferInstance p x Dg g M R₀ R₁ hp (R:=Q.P) hk hs hq (u i) ?_ ?_ hy U hU hz
    · intro x hx z ht; exact portionU _ _ i|>.1 (hR.watch i x (by rw [portionU]; rw [he] at hx; exact hx) z ht)
    exact ht
lemma lowU (hk:k ≤ D)(hv:d ≤ D)(hq:Factor w D g.count μ): ‖(wP*(Cp*chalkW c R₁*(Cp).transpose)*(sP).transpose) () ()‖ ≤ C*μ^2:=by exact idea inferInstance inferInstance p p' x y Dg g M R₀ R₁ hp hv hk hq
omit Dg hp
lemma priceG (DF:Eyes su D L (2*n) j a v b ε s C) (hk:k ≤ D)(hd:d ≤ D) (hV: Grain a v b R₀ f)(hw:1 ≤ w): ‖(wP*chalkW f R₀*(sP).transpose) () ()‖ ≤ billN w D*(billN w D*C):= by exact violet inferInstance p p' x y DF hk hd R₀ hV hw
open YM.Bloom.Jar YM.Bank.Jule
lemma view_read (H: Acquired su D n a v b ε s C w f)(hk:k ≤ D)(hd:d ≤ D) (hp:Grain a v b R₀ f) (hv:posT w (2*n) (x-y)∈ Oasis ε s): ‖(pots (w^n) f p x*chalkW f R₀*(pots (w^n) f p' y).transpose) () ()-viewK p p' (posT w (2*n) (x-y))‖≤ C/w:=by exact pens inferInstance p p' x y H hk hd _ hp hv
lemma wears (Dg:Eyes su D L (2*n) j a v b ε s C)(hk:k ≤ D)(hw: 1 ≤ w): cusp wP () ≤ billN w D*C:= by exact YM.Bloom.marks inferInstance p x Dg hk hw
section
attribute [-instance] Sample.LoomT.instFintypeTo
variable {pv: Clip}
lemma graced (hp:R₀.covered v b) (ht: Floor R₀ pv f a b): Grain a v b R₀ f:=⟨hp.2.1,ht.uniform.1,ht.starts⟩
lemma highG (hp : ∃ W V,YM.Bank.TowerW j g R₀ R₁ M W V)(ht: Grain a v b R₀ f)(hz: Grain a v b R₁ c)(he:0<v): YM.Bloom.Fare j a b g M R₀ R₁:=⟨hp, Bloch.Row.rights _ _ ht.strip he.le,⟨_,he.le,hz.strip⟩,⟨_,ht.noteN,hz.noteN⟩⟩
lemma fullSymm (ht:Floor R₀ pv f a b)(he:0<a): (chalkW f R₀).IsSymm:=Matrix.IsSymm.map (Fruit.chargedC su R₀ f ht he) _
attribute [instance] Sample.LoomT.instFintypeTo
end
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.lightU
#print axioms YM.MassiveQCD.Inky.lowU

#print axioms YM.MassiveQCD.Inky.priceG
#print axioms YM.MassiveQCD.Inky.highG
