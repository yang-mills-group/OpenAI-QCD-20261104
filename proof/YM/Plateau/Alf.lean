import YM.Plateau.Tea
import YM.Sprig.Icar
import YM.Plateau.Hero
import YM.Plateau.Crake
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

-- analytic weights in original calibration metrics. independent of β and Omega geometry.Chi.

-- One geometry for ANY P; auxiliary lattice can be selected earlier. no parameters from later volume or comparator needed to set accuracy.
lemma blunt (t:Bool)(d:ℕ):∃ H: Label d→ₗ[ℂ]Label d, Ami d p q g t H:=by
      obtain ⟨i,C,P,m,w,hx,hP,hC,hP',h',_,_,he⟩:= (QCD.Acre.Stratum.MarchQ.Suburb.Melt.Calendar.JuneP.intense _ zero_lt_one).exists; obtain ⟨n,hn⟩:=he d
      exact nature (P:=P) d hP' n hn _ _ _ _ -- order check
lemma pavilion :∃ (Kc:Flavor 6→Flavor 6→Bool→ℝ)(Vw:Flavor 6→Flavor 6→Bool → (Label 8→ₗ[ℂ]Label 8))(H:ℝ), 1≤H∧∀ p q:Flavor 6,∀ g:Bool,Ami 8 p q g true (Vw p q g) ∧ Kc p q g* ‖(Vw p q g).toContinuousLinearMap‖ ≤ H ∧ 0<Kc p q g ∧∀ x y z:ℂ, ‖x‖+‖y‖+‖z‖≤Kc p q g*‖Style p q g x y z‖:=by
      choose Vw hV using fun p q g=> blunt p q g true 8
      choose Kc hc hC using fun p q g=> face_cost p q g
      let W(p: Flavor 6 × Flavor 6 × Bool):=Kc p.1 p.2.1 p.2.2* ‖(Vw p.1 p.2.1 p.2.2).toContinuousLinearMap‖
      obtain ⟨H,hH⟩:= (Set.finite_range W).bddAbove; exact ⟨Kc,Vw,max H 1,le_max_right ..,fun p q g=>⟨hV p q g, le_trans (show W (p,q,g) ≤ H from hH ⟨_,rfl⟩) (le_max_left ..),hc ..,hC p q g⟩⟩
end YM.Sprig
#print axioms YM.Sprig.pavilion
