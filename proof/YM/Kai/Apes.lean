import YM.Kai.Stray
import YM.Plateau.Alf
/-! L2 projection family tolerance.N0 independent TRACK parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open YM.Sprig Tarn Tarn.Choir Pollens
open Patria.Rolls Poised.Stative Poised.Plans Poised.Plans.Stamp
local notation "Z"=> RawVec 10
lemma starP : ∃ P:(Axis→Label 10)→ₗ[ℂ](Axis→Label 10), Tackle 10 claw P:=by
    obtain ⟨i,C,P,m,w,hx,hP,hC,hP',h',_,_,he⟩:= (QCD.Acre.Stratum.MarchQ.Suburb.Melt.Calendar.JuneP.intense _ zero_lt_one).exists; obtain ⟨n,hn⟩:=he 10; exact paddle _ claw n hP' hn
variable {C:Sequence}{P:Calibration C}(F:Tarn.Choir)(T:Pollens P F)
noncomputable abbrev curtain(F:Choir) := twix 10 (fun i=>F.focus (shelV i) 10)
include T
lemma befalls (h: F.Domestic)(V:(Axis→Label 10)→ₗ[ℂ](Axis→ Label 10))(hp:Tackle 10 claw V)(z:Z)(δ:ℝ)(hδ:0≤δ)(he:∀ i:Axis,∃ x:Label 10,F.focus (shelV i) 10 x=0∧‖z.val i-x‖ ≤δ) :∃ p:Z,bits F p=0∧‖z-p‖≤ ‖V.toContinuousLinearMap‖*δ :=by
     choose g hg ht using he; let p:Z:=⟨V g,hp.root _⟩; let M:= (curtain F).ker; have hL(i:Axe)(x:Axis→Label 10): curtain F (roar claw P.sym 10 i x)= lion T claw i (curtain F x):= funext fun j=> (calmP T claw 10 _ equalV (fun _=>rfl)).spin ..
     have he': V g∈M:=(hp.pays M P.sym (fun x i=>by change curtain F x=0 ↔ curtain F _=0; rw[hL]; exact ⟨fun h=> by rw [h, map_zero],fun h=> (lion T claw i).injective (h.trans (map_zero _).symm)⟩)).1 g (funext hg)
     let L:=V.toContinuousLinearMap; have hr:V z.val= z.val:= hp.same _ z.property; refine ⟨p, he', ?_⟩; have hb: ‖z.val-g‖ ≤δ:= (pi_norm_le_iff_of_nonneg hδ).mpr ht; change ‖(z.val-p.val)‖ ≤ _; rw[← hr]; change ‖L z.val - L g‖≤ _; rw [←map_sub]; exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
end YM.Massive.Patria.Gall.Onyx
#print axioms YM.Massive.Patria.Gall.Onyx.befalls
#print axioms YM.Massive.Patria.Gall.Onyx.starP
