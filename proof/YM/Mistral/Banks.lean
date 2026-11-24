import YM.Mistral.Garb
import YM.Alum.Fur
import YM.Alum.Fables
/- Ax.R ψ footprint specialized. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub.Duon
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth Intag Next.Rank.Station
open Lyre Goblet Needle
variable {S:Massive.Scheme}{R:Side}{m j ℓ P N:ℕ}
local notation "F"=>S.side R N
variable (B:Regulator (S.side R N) 6)
local notation "Tt" j:arg=> S.spacing j
local notation "Dϕ"=> viewW S R
local notation "qS"=> ratioTo S N ℓ
variable (z:Site (S.side R ℓ))(he:Even R.val)(hj:j≤ℓ)(hN:ℓ≤ N)(p:Site (S.side R j))
local notation "TΓ"=> Intag.Column.sky S R j N (hj.trans hN) (evenW S R he j) z
local notation "T₀"=> Intag.Column.sky S R j ℓ hj (evenW S R he j) z
variable (d:ℕ) (Θ:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(Y:Sequence)(Q:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
-- margin from nearest summit.P.B☆. Need positivity.Z. Floors receipts use Ò.
local notation "Ωp" w:arg b:arg=> Bloom Uv d F b w
variable (hC:Tarot.Vista.kingT ((Uv.display Y Θ Q U base).stencil d) ≤ ratioTo S N ℓ)
include hC
open QCD.Plum
lemma granted (w:UV.Label d)(b:Cover)(q:Bool)(hp:moored w.val q)(hx:(viewW S R hN).parent (wrap F b) ∈ (T₀).margin p 2) : Fence ((TΓ).chamber p) (Ωp w b) ∧ ∀ V,Hom q ((Ωp w b) V):=by
       let g:= viewW S R hN; have hz:= Tarot.Vista.kingFlow Uv Θ Q Y U base b TΓ p (g.count.val*1) w q hp (smeared R he hj hN 1 z p _ hx) (by rw [mul_one]; exact hC) rfl
       exact hz.2
lemma charged (w:UV.Label d)(b:Cover)(q:Bool)(hp:moored w.val q)(hx:(viewW S R hN).parent (wrap F b) ∈ (T₀).margin p 2)(hr:B.t=0)(u:ℝ)(hu:floorL TΓ B.average B (Ωp w b) p≤u): Gold B TΓ p (Ωp w b) u:=by obtain ⟨h,hP⟩:= granted z he hj hN p d Θ Uv Y Q base U hC w b q hp hx; apply Gold.mono (coin h ⟨_,hP⟩); rw [← sprouts _ _ _ _ hr]; exact hu
lemma diffracts (w x:UV.Label d)(b c:Cover)(q:Bool)(hp:moored w.val q)(hq:moored x.val q)(hb:(viewW S R hN).parent (wrap F b)∈ (T₀).margin p 2)(hx:(viewW S R hN).parent (wrap F c)∈ (T₀).margin p 2)(hr:B.t=0)(u:ℝ)(hv:floorL TΓ B.average B (Ωp w b-Ωp x c) p≤u): Gold B TΓ p (Ωp w b-Ωp x c) u:=by
      obtain ⟨hf,hP⟩:= granted z he hj hN p d Θ Uv Y Q base U hC w b q hp hb; obtain ⟨hX,hV⟩:= granted z he hj hN p d Θ Uv Y Q base U hC x c q hq hx
      have he:Fence ((TΓ).chamber p) (⇑(Ωp w b-Ωp x c)):=by change Fence _ (⇑(Ωp w b)-⇑(Ωp x c)); rw [sub_eq_add_neg]; exact hf.add (postsNeg hX)
      let y:Insertion F 6:= Ωp w b-Ωp x c; have hz:Potion (⇑y):= ⟨q,fun U=>by unfold y; change Hom q (((Ωp w b) U)-((Ωp x c) U)); rw [sub_eq_add_neg]; exact (hP U).add (homNeg (x:=⇑(Ωp x c)) (hV U))⟩
      apply Gold.mono (coin he hz); rw [← sprouts _ _ _ _ hr]; exact hv
lemma charge3 (w x y:UV.Label d)(b c:Cover)(q:Bool)(hp:moored w.val q)(hq:moored x.val false)(hS:moored y.val q)(hb:(viewW S R hN).parent (wrap F b)∈ (T₀).margin p 2)(hx:(viewW S R hN).parent (wrap F c)∈ (T₀).margin p 2)(hr:B.t=0)(r:ℂ)(u:ℝ)(hv:floorL TΓ B.average B (r • (Ωp w b* Ωp x c)-Ωp y b) p ≤ u): Gold B TΓ p (r • (Ωp w b*Ωp x c)-Ωp y b) u:=by
       obtain ⟨hF,hP⟩:= granted z he hj hN p d Θ Uv Y Q base U hC w b q hp hb; obtain ⟨hX,hV⟩:= granted z he hj hN p d Θ Uv Y Q base U hC x c false hq hx; obtain ⟨hY,hD⟩:= granted z he hj hN p d Θ Uv Y Q base U hC y b q hS hb
       let f:Insertion F 6:= r • ((Ωp w b)*(Ωp x c))-Ωp y b
       have he : Fence ((TΓ).chamber p) ⇑f:=by change Fence _ (r • (⇑(Ωp w b)*⇑(Ωp x c))-⇑(Ωp y b)); rw[sub_eq_add_neg]; exact (((hF.mult hX).mass _).add (postsNeg hY))
       have hP' (V:Grid F):Hom q (f V):=by change Hom _ (r • (((Ωp w b) V)*((Ωp x c) V))-_); have h:= (hP V).mul (hV V); simp only [Bool.xor_false] at h; rw [sub_eq_add_neg]; exact (h.smul _).add (homNeg (x:=⇑(Ωp y b)) (hD V))
       apply Gold.mono (coin he ⟨_,hP'⟩); rw [← sprouts _ _ _ _ hr]; exact hv
end YM.Massive.Patria.Hub.Duon
#print axioms YM.Massive.Patria.Hub.Duon.charge3
#print axioms YM.Massive.Patria.Hub.Duon.charged
#print axioms YM.Massive.Patria.Hub.Duon.diffracts
