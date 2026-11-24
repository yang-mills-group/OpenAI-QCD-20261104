import YM.QCD.Sage.Primo
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Nuts
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sage
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Baffle Prism Brim Lotus Peak
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c}
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (hp : Intake P T X.x R)
  (hs : Scrim X a) (hP : Room P S T X.x)
variable {W : Config G f} {ζ d A t : ℝ} (h : Canary G d A) (hv : Drivable X d A V)


def kernel := a.received X.k T q b (gStep R.beta) X.V 1 0 -- F origin
def pasture (z : Prices G I):= strip6 X a X.V (anchor X a z R.beta)
lemma frozenB (B:BudgetPoint){n:ℕ}(C:Libretto G n)(D:Record)(hv:Plays C D B R.p P T X.x)(ht:Healthy B.threshold Y X.V)(hr:0<R.beta) : Healthy R.p.threshold (R.activities.reg i).support (kernel X i R a q b):= Baffle.lampLife X a hr hv ht q b (p:=0) (by rw [show tape (0:Prices G I)=(0:LogArray G I) from rfl,norm_zero,mul_zero]; positivity [D.guards,R.p.threshold_pos])
variable {K M η ρ Q:ℝ}
include hs
lemma plant (z:Prices G I) (hv: ‖z‖≤M) (ht :0<R.beta)
    (hw:∀ y:G.Color, ‖y‖ ≤ η → G.chord (G.lieExp y) ≤ ρ*‖y‖)(hQ:0≤Q)
    (hq:Q≤η)(he:∀ j, ‖volume6 X a j X.V‖+gStep R.beta*((Fintype.card G.ColorIndex:ℝ)*M) ≤ Q)
    (hf:∀ j, ‖volume9 X a q 1 b j X.V‖ ≤ Q)(hρ:0≤ρ):
    ∀ j:Bond f,j.1 ∈ inspected (R.activities.reg i).support → j.1+step j.2 ∈ inspected (R.activities.reg i).support → G.chord (pasture X i R a z j*(kernel X i R a q b j)⁻¹) ≤ ρ*Q+ρ*Q:=by
    obtain ⟨J,B,H⟩:= Eider.weave G
    let y:= -(distance9 X X.V a q b R.beta); have hu: reading9 X X.V a y q b J R.beta=0:=by rw [reading9,fast_zero X a H ht, neg_add_cancel] -- adjust
    intro j hj hk
    let V:= pasture X i R a; have hy : kernel X i R a q b j=V y j:=by unfold kernel; rw [← hu]; have hf:= hears9 X X.V a ht hs y q b J j hj hk; rwa [reading6, fast_zero X a H ht] at hf
    rw [hy]; by_cases hh : j∈F.trunks
    · have h(u): V u j =1:=F.on_tree _ ⟨j,hh⟩; rw [show pasture X i R a z j=1 from h z,h y,inv_one,mul_one,G.chord_one]; positivity
    obtain ⟨j',hf'⟩:= falls X a ⟨j,hh⟩ hj hk; change a.address j'=j at hf'; subst j
    let e:=a.address j'; let u:=anchor X a z R.beta j'; let w:= anchor X a y R.beta j'
    have hz : ‖u‖ ≤ Q:=by
       have hh:= color_cover (show 0 ≤ M from (norm_nonneg _).trans hv) (tape z j') (fun g=> (norm_le_pi_norm z (j',g)).trans hv)
       apply (norm_add_le ..).trans; rw [norm_smul,Real.norm_of_nonneg (show 0≤gStep R.beta from inv_nonneg.mpr (Real.sqrt_nonneg R.beta))]; exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Real.sqrt_nonneg _)))).trans (he j')
    have hb: w=volume9 X a q 1 b j' X.V:=by unfold w; rw [← sunny X a H y, ← credits X a ht y q X.V b J,hu,show tape (0:Prices G I)=(0:LogArray G I) from rfl]; simp
    have h1: ‖w‖ ≤ Q:=hb ▸ hf j' -- syntax
    have h (p:Prices G I):V p e =increment _ (isotope X a (anchor X a p R.beta)) e := X.viewing _ _ (borne X a hs j') -- replica infer
    change G.chord (V z e * (V y e)⁻¹) ≤_
    rw [h z,h y]; unfold increment; simp_rw [show ∀ p:Prices G I, isotope X a (anchor X a p R.beta) e =_ from fun p=> tap X a j' _] -- explicit
    rw [_root_.mul_inv_rev, ← mul_assoc,mul_inv_cancel_right]
    refine (G.chord_triangle _ _).trans (add_le_add ((hw u (hz.trans hq)).trans (mul_le_mul_of_nonneg_left hz hρ)) ?_); rw [G.chord_inv]; exact (hw w (h1.trans hq)).trans (mul_le_mul_of_nonneg_left h1 hρ)
end YM.PhysicalNext.Repeat.Sage
