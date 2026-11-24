import YM.Mural.Shield
import YM.Mural.Arch
import YM.Mural.Quail
/-! # Corona scaling for the single use. Form ledger enough. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet.Glow
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {P:Teller su}{L:Side}{μ C δ α θ:ℝ}
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph Jets.Touch
variable (Q:Target su P)

open Mural MassiveQCD.Apron
abbrev bTop (L:Side)(x:ℝ) := betaF su x L^((7/40):ℝ) -- each Letter. 2 extra.
abbrev phaseR (L:Side)(x:ℝ):=betaF su x L^(-(3/8):ℝ)
-- all within impulses.Second
variable (L θ)
lemma b_tops (he:0<θ) : ∀ᶠ x in atTop, 1 ≤ betaF su x L ∧ ∀ b:ℝ,1≤b→ b ≤ bTop L x→ b^2* phaseR L x ≤ fundsL L θ x ∧ fundsL L θ x≤1 ∧ b^4*Real.exp (fan L (1/4) x) ≤ Real.exp (fan L (1/4) x*2):=by
    have hl: Rate su L (-1/40) (fun x=>(bTop L x)^2*phaseR L x):=((Rate.power.pow 2).mul Rate.power).weaken (by norm_num)
    have hh: Jets.Touch.Seat L (-θ-1) _ := Seat.eliminated hl (by linarith)
    have hp : Rate su L (7/10) (fun x=> bTop L x^4):=(Rate.power.pow 4).weaken (by norm_num)
    have hv: Rate su L (-(17/10)) (fun x=>Real.exp (-1*fan L (1/4) x)):=Rate.monitor_cutoff zero_lt_one (by norm_num)
    filter_upwards [(Work.E09.betaF_growth su L).eventually_ge_atTop 1,hh (-θ) (by linarith), (Seat.keeps (L:=L) (a:=-θ)).shrinks (by linarith) one_pos, (hp.mul hv).below (by norm_num) 1 one_pos] with x hx hh hs hw
    refine ⟨hx, fun b hz ht=>?_⟩; have hb:=zero_le_one.trans hz; have hp : Real.exp (-(fan L (1/4) x))= (Real.exp (fan L (1/4) x))⁻¹:=by rw [Real.exp_neg]
    refine ⟨(mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb ht _) (Real.rpow_nonneg (zero_le_one.trans hx) _)).trans ((le_abs_self _).trans hh), (le_abs_self _).trans hs,?_⟩
    have hf:bTop L x ^ 4*Real.exp (-1*fan L (1/4) x) ≤ 1:= (le_abs_self _).trans hw; rw [neg_one_mul,hp,← div_eq_mul_inv] at hf
    rw [show fan L _ _ * (2:ℝ)=_ from mul_two _,Real.exp_add]; exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ hb ht 4).trans ((div_le_one (Real.exp_pos _)).mp hf)) (Real.exp_pos _).le
abbrev EPrice (Q:Target su P)(X:ℝ):= X/(Real.exp 1*Real.exp ((Q.relative+1)*Footprint.preCost 38))
abbrev payFee (L:Side)(θ:ℝ)(x:ℝ):= EPrice Q (fundsL L θ x)
lemma feePower (x:ℝ):0<payFee Q L θ x ∧ payFee Q L θ x* (Real.exp 1*Real.exp ((Q.relative+1)*Footprint.preCost 38))= fundsL L θ x ∧ payFee Q L θ x≤fundsL L θ x:=by
    unfold payFee EPrice; have hf:0<fundsL L θ x:=fan_pos ..; have he:0 ≤ Q.relative:=by unfold Target.relative; linarith [Q.bound,Q.usable,Q.pos]
    refine ⟨by positivity,div_mul_cancel₀ _ (mul_ne_zero (Real.exp_pos _).ne' (Real.exp_pos _).ne'), div_le_self hf.le (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one) (Real.one_le_exp (mul_nonneg (by linarith only [he]) (by unfold Footprint.preCost; positivity))))⟩
end YM.QCD.Loom.Fleet.Glow
#print axioms YM.QCD.Loom.Fleet.Glow.feePower
#print axioms YM.QCD.Loom.Fleet.Glow.b_tops
