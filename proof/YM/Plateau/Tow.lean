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

variable (R: Flavor 6→ℝ)(μ δ φ₂ η:ℝ)
-- exact bill affidavit.
noncomputable abbrev lever (Q:Choir):= Q.focus MassFields.isotropic 8 (flame p q g 8 (by decide))
local notation "Z0"=> lever p q g Q
noncomputable abbrev axisP (Q:Choir)(i:Axis):= Q.focus (MassFields.atVector i) 6 (UV.mesonCode 6 p q (claw g i) (by decide))
local notation "A"=> axisP p q g Q
noncomputable def aimV (Q:Choir):=∑ i:Bool,Q.focus MassFields.isotropic 8 (arbor p q g i)
local notation "Ω"=> aimV p q g Q
lemma armp : aimV p q g Q=Q.focus V 8 U+Q.focus V 8 W₀:=by rw [aimV,Fintype.sum_bool]
variable (X: ℝ)(hg:∀ i:Axis, Q.arc i (axisP p q g Q i) = Q.focus MassFields.isotropic 8 (stereo p q i (claw g i)))
include hg
lemma bodies : ∑ i:Axis,Q.arc i (axisP p q g Q i)= aimV p q g Q:=by
      rw [armp,←map_add]; simp_rw [hg, ←map_sum]; apply congr_arg; unfold Massive.Oriole.stereo; rw [Finset.sum_add_distrib]; rfl
omit hg
include h6 hp hf6 H
lemma torch (i:Axis) : axisP p q g Q i≠0:=rate6 T p q g H _ h6 hp hf6 _ (fun h=> by have hp:= (claw_unit g i).2; rw [h] at hp; simp at hp) -- edit private hunit
variable (C1p X1 Y1:Bool→ℂ)
omit h6 hp hf6 H
noncomputable abbrev μν (p q:Flavor 6)(r: Flavor 6→ℝ)(s:Bool):= r (if s then q else p)
local notation "vP"=>μν p q R
noncomputable abbrev markK(p q:Flavor 6)(g:Bool)(R:Flavor 6→ℝ):ℝ:= if g then R p+R q else R p-R q
structure Honors (Q:Choir)(p q:Flavor 6)(g:Bool)(R: Flavor 6→ℝ)(u:ℝ) (c:ℂ):Prop where
     nonzero : lever p q g Q≠0
     room : lever p q g Q ∈ Q.level 6
     stars : aimV p q g Q=c • lever p q g Q
     fee : ‖c- (markK p q g R:ℂ)‖ ≤ u
variable (hX:∀ s, ‖C1p s+(μν p q R s:ℂ)‖≤ X)(hv:∀ s, ‖X1 s-parL s g‖+‖Y1 s-parR s g‖ ≤ δ)(hh:∀ s,Q.focus MassFields.isotropic 8 (Style p q g (C1p s) (X1 s) (Y1 s))=0) -- Z notation!
include h6 h8 hf6 hf8 H hp hX hv hh
lemma given (hδ:0≤ δ)(hD:δ≤1/4)(hA:∀ s,|μν p q R s|≤μ)(hr:2*(X+δ*(4*(X+μ))) ≤ φ₂):∃ c:ℂ,Honors Q p q g R φ₂ c:=by
      have hμ:∀ s,‖(μν p q R s:ℂ)‖ ≤μ:=fun s=>by rw[Complex.norm_real]; exact hA s
      obtain ⟨h1,h2,w,hW,hV⟩:= signalR T p q g h8 h6 hf8 hf6 H hp C1p X1 Y1 hh δ hδ hv (μν p q R) μ X hX hμ hD
      refine ⟨w,h1,h2,(armp p q g (Q:=Q)).trans hW,?_⟩; have he : (markK p q g R:ℂ) = (vP false:ℂ)+poli g * (vP true:ℂ):=by cases g<;>simp [markK,μν,poli] <;> ring
      rw [he]; exact hV.trans hr
omit h6 h8 hf6 hf8 H hp hX hv hh
variable {c c':ℂ}(hvR: Honors Q p q g R φ₂ c)(hz:Honors Q q p g R φ₂ c') -- hv shadow warn include.H
include T hvR hz
lemma crossingL : c=poli g*c' ∧ c=(c.re:ℂ):=by
    let F:= Z; let Up:= Q.focus MassFields.isotropic 8 (flame q p g 8 (by decide)); let i:= timeAxis
    have h1:T.charge (lever p q g Q)=Up:=by rw[lever,T.c]; apply congr_arg; exact woke ..
    have h2:T.adj i (lever p q g Q)=(-poli g) • Up:=by
           unfold lever; rw [T.a,Massive.Oriole.yaw, map_smul]; -- edit
    have hV: aimV p q g Q= c • Z0:=hvR.stars
    have hA: T.charge (aimV p q g Q)=poli g • (aimV q p g Q):=by
           rw [armp,armp,map_add,T.c,T.c, rayU, rayU,map_smul,map_smul,smul_add,add_comm]; rfl -- p
    have hS : T.adj i (aimV p q g Q)= -(aimV q p g Q):=by
           rw [armp,armp,map_add,T.a,T.a,riseQ,riseQ,map_neg,map_neg,neg_add,add_comm]; rfl
    rw [hV,map_smul,h1,hz.stars,smul_smul] at hA; have hC:c=poli g*c':= smul_left_injective ℂ hz.nonzero hA
    refine ⟨hC,?_⟩; rw [hV,map_smulₛₗ,h2,smul_smul,hz.stars,← neg_smul] at hS; have hb:(star c)*(-poli g)= -c':= smul_left_injective ℂ hz.nonzero hS; have he:star c=c:=by
           cases g; · simp [poli] at hb hC; exact hb.trans hC.symm
           simpa [poli,show c'=c from by simpa [poli] using hC.symm] using hb
    refine Complex.ext (by simp) ?_; change c.im=_; have h:= congr_arg Complex.im he; change -c.im=c.im at h; rw [Complex.ofReal_im]; linarith
end YM.Sprig
#print axioms YM.Sprig.torch
#print axioms YM.Sprig.given
#print axioms YM.Sprig.crossingL
#print axioms YM.Sprig.bodies
