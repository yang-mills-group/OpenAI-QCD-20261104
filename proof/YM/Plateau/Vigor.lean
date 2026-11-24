import YM.Plateau.Tow
import YM.Plateau.Hero
import YM.Plateau.Crake
import YM.Oriole.Stoop
import YM.Plateau.Rock
import YM.Plateau.Phlox
/-! # Rank and the two equations. Genuine small gaps vs margin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
variable (p q:Flavor 6)(g:Bool)
open Massive.Oriole Compass Submodule
variable {J8:Label 8→ₗ[ℂ]Label 8}{J6:Label 6→ₗ[ℂ] Label 6} (h8:Ami 8 p q g true J8)(h6:Ami 6 p q g false J6)
variable {F8: UV.Free.Symbol 8≃ₗ[ℂ](Q.level 8)}(hf8:Prose F8 T){F6: UV.Free.Symbol 6≃ₗ[ℂ](Q.level 6)}(hf6:Prose F6 T)
local notation "V"=>MassFields.isotropic
local notation "Z"=> Q.focus MassFields.isotropic 8
local notation "K"=> p
local notation "M"=> flame p q g 8 (by decide)
local notation "U"=> arbor p q g true
local notation "W₀"=> arbor p q g false
local notation "P★"=> prismT F8 M
variable (H: Q.Domestic)(hp:p≠q)


variable (R: Flavor 6→ℝ)(dε δ ψ ξ:ℝ)
abbrev PlumR (s:Bool)(δ ξ:ℝ):Prop:= ∃ x y z:ℂ,Q.focus MassFields.isotropic 8 (Style p q g x y z)=0∧ ‖x + (μν p q R s:ℂ)‖ ≤ ξ∧ ‖y-parL s g‖+‖z-parR s g‖ ≤ δ
#print PlumR
variable (hΦ:∀ s:Bool,PlumR (Q:=Q) p q g R s δ ξ)
include hΦ H h6 h8 hf6 hf8 hp
lemma presence (hδ:0≤δ)(hh:δ≤1/4)(ht:∀ s,|μν p q R s|≤ ψ)(hD:2*(ξ+δ*(4*(ξ+ψ)))≤dε): ∃ c:ℂ,Honors Q p q g R dε c:=by
     choose c y z h hc hQ using hΦ; exact given T p q g h8 h6 hf8 hf6 H hp R ψ δ dε ξ c y z hc hQ h hδ hh ht hD -- inspect
omit hΦ H h6 h8 hf6 hf8 hp
variable (hPQ:∀ (p q:Flavor 6)(g:Bool),p≠q→∃ c:ℂ,Honors Q p q g R dε c)
include hPQ T
lemma certified : ∃ c: Flavor 6→ Flavor 6→Bool→ℝ,(∀ p q g,c p q g= if g then c q p g else -c q p g)∧∀ p q g,p≠q→ Honors Q p q g R dε (c p q g:ℂ):=by
      choose! x hx using hPQ; let c(p q:Flavor 6)(g:Bool):= if p=q then (0:ℝ) else (x p q g).re; have h(p q:Flavor 6)(g:Bool)(hp:p≠q): (c p q g:ℂ)= x p q g:=by unfold c; rw [if_neg hp]; exact (crossingL T p q g R dε (hx p q g hp) (hx q p g hp.symm)).2.symm
      refine ⟨c,fun p q g=>?_,fun p q g hp=> (h p q g hp).symm ▸ hx p q g hp⟩
      by_cases hp:p=q; · subst p; simp [c]
      have ht: (c p q g:ℂ) = poli g*(c q p g:ℂ):=by rw [h p q g hp,h q p g (Ne.symm hp)]; exact (crossingL T p q g R dε (hx p q g hp) (hx q p g (Ne.symm hp))).1
      cases g <;> simpa only [Bool.false_eq_true,↓reduceIte,poli,one_mul,neg_one_mul, ← Complex.ofReal_neg, Complex.ofReal_inj] using ht
end YM.Sprig
#print axioms YM.Sprig.certified
#print axioms YM.Sprig.presence
