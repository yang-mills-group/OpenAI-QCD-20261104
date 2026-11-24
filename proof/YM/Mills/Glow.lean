import YM.QCD.House.Plenary
import YM.Mills.Spoors
/-! # purchases with augmented optional weights. Facts enforced literally. -/
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
-- augmented uses K. Need assert hires rate hQ.rate.
def leanX (L:Side)(θ x:ℝ):=fundsL L θ x*(1-(1/2:ℝ))⁻¹+(betaF su x L^(-(3/8):ℝ)+ betaF su x L ^(-(3/8):ℝ))
def simple (L:Side)(μ C θ β x:ℝ):= Pipe.unitsP Q L μ β x C (shiftCost L x (romp L)) (leanX L θ x)
def levelX (L:Side)(θ x:ℝ):=fundsL L θ x*(1-(1/2:ℝ))⁻¹+(lantern L x*betaF su x L^(-(3/8):ℝ)+lantern L x*betaF su x L^(-(3/8):ℝ))
def joined (L:Side)(θ x:ℝ):= lantern L x*Q.goal L x + levelX L θ x
def billsV (L:Side)(μ C θ β x:ℝ):= Buy.quote su L μ (1/2) Q.exp Q.ε Q.δ β x (lantern L x) 0 (C*Delay.bill su L x^5 + shiftCost L x (romp L)) (joined Q L θ x)
lemma hoist (L:Side)(θ:ℝ)(hh:Q.rate ≤ -(3/8:ℝ)) : Jets.Touch.Seat L (-θ) (joined Q L θ) :=by
    have hz : Rate su L (1/8) (lantern L):=Rate.power
    have hk: Jets.Touch.Seat L (-θ) (fun x=>lantern L x* betaF su x L ^ (-(3/8):ℝ)):=Seat.eliminated (hz.mul Rate.power) (by norm_num)
    exact (Seat.eliminated (hz.mul (show Rate su L _ (Q.goal L) from Rate.power)) (by linarith)).comb ((Seat.keeps.times ((1-(1/2:ℝ))⁻¹)).comb (hk.comb hk))
lemma lite (L:Side)(θ:ℝ)(x:ℝ)(hp:0<betaF su x L)(h:1≤lantern L x) : 0 ≤ Q.goal L x+leanX L θ x ∧ Q.goal L x+leanX L θ x ≤ joined Q L θ x:=by
    have h₀:0 ≤ Q.goal L x:= Real.rpow_nonneg hp.le _
    have hΩ:0 ≤ betaF su x L^(-(3/8):ℝ):= by positivity
    have hD:0≤fundsL L θ x:=(fan_pos ..).le
    refine ⟨by unfold leanX; positivity,?_⟩
    have hz:= le_mul_of_one_le_left hΩ h; exact add_le_add (le_mul_of_one_le_left h₀ h) (add_le_add le_rfl (add_le_add hz hz))
lemma tolerance_now (L:Side)(θ:ℝ)(hh:Q.rate ≤ -(3/8:ℝ))(he:0<θ): ∀ᶠ x:ℝ in atTop, joined Q L θ x ≤ Buy.tolerance Q.δ (radiusB x):=by
    have hz: Jets.Touch.Seat L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)):=by simpa only [one_mul] using expensed (L:=L) 0 1 0
    filter_upwards [((hoist Q L θ hh).ponies (hz.timesL 16)).shrinks (by linarith) Q.pos] with x hx
    exact (le_div_iff₀ (show 0 < 16*(Animals.ballCost (radiusB x):ℝ) by have := Animals.neighbors_ge (radiusB x); positivity)).2 ((le_abs_self _).trans hx)
private lemma cap_bills (L:Side){C:ℝ}(hC:0≤C):∀ᶠ x:ℝ in atTop, lantern L x ≤ Real.exp ((C+1)*Delay.bill su L x^5*Delay.fineMonitor su L x^(1:ℝ)):=by
   filter_upwards [Jets.Touch.upperTax L 1 (by norm_num) (lantern L) _ (Rate.power (G:=su) (L:=L) (a:=(1/8:ℝ))), (Seat.your L).eventually_ge_atTop 1] with x hx he
   apply hx.trans; apply Real.exp_monotone; rw [one_mul,Real.rpow_one]; apply le_trans (le_mul_of_one_le_left (fan_pos ..).le (show 1 ≤ (C+1)*Delay.bill su L x^5 from one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (Delay.bill_ge ..))))
   refine mul_le_mul_of_nonneg_left ?_ (by positivity [Delay.bill_ge su L x])
   exact (Real.rpow_le_rpow_of_exponent_le he (by norm_num : (1/3:ℝ)≤1)).trans_eq (Real.rpow_one _)
lemma royalties (L:Side)(θ:ℝ)(hh:Q.rate ≤ -(3/8:ℝ))(he:0<θ)(hm:0<μ)(hC:0≤C):∀ᶠ x:ℝ in atTop, ∀ β:ℝ, betaF su x L/2 ≤β → (simple Q L μ C θ β x).Buy L Q.halo (radiusB x)∧ (billsV Q L μ C θ β x).Buy L Q.halo (radiusB x):=by
   filter_upwards [Buy.quoted su L hm (show (0:ℝ)<1/2 by norm_num) Q.pos Q.bound Q.usable (show 0 ≤ C+1 by linarith) (by norm_num : (1:ℝ)<2) 5 Q.halo, (Work.E09.betaF_growth su L).eventually_ge_atTop 1,tolerance_now Q L θ hh he, taken L (romp L),cap_bills L hC] with x hx he ht hP hs β hβ
   have hf: Delay.fineMonitor su L x ≥1:= Real.one_le_exp (sq_nonneg _)
   have hw :0 ≤ Delay.bill su L x^5:=by have h:= Delay.bill_ge su L x; positivity
   have hΛ:1≤lantern L x:= Real.one_le_rpow he (by norm_num)
   have hg:= lite Q L θ x hx.1 hΛ
   let p:= hx.2; have h : (simple Q L μ C θ β x).Buy L Q.halo (radiusB x):=by
       refine p _ 1 0 _ _ (by linarith only [hβ]) le_rfl zero_le_one (hΛ.trans hs) ?_ hg.1 (hg.2.trans ht)
       rw [mul_zero,add_zero,Real.rpow_one,add_mul,one_mul,add_mul]; exact add_le_add (le_mul_of_one_le_right (mul_nonneg hC hw) hf) (hP.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (Delay.bill_ge ..))))
   refine ⟨h,p _ _ 0 _ _ (by linarith only [hβ]) le_rfl (zero_le_one.trans hΛ) hs ?_ (hg.1.trans hg.2) ht⟩
   rw [mul_zero,add_zero,Real.rpow_one,add_mul,one_mul,add_mul]; exact add_le_add (le_mul_of_one_le_right (mul_nonneg hC hw) hf) (hP.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (Delay.bill_ge ..))))
private lemma framer (Z : ℝ→ℝ→ Costs) {θ:ℝ} (hv:0<θ)(hz:0 ≤ α)(he:α+1+1≤Q.exp) (h : ∀ x β, (Z x β).exponent=Q.exp) (hw:∀ x β, apple (Z x 0)=apple (Z x β)) (hh:∀ᶠ x:ℝ in atTop, 0 < apple (Z x 0)) (hS:Jets.Touch.Seat L (-θ) (fun x=>apple (Z x 0))) : ∀ᶠ x:ℝ in atTop, ∀ β:ℝ, Corner Q (radiusB x) (Z x β) α:=by
   let t x:=apple (Z x 0); let f x:=barley (Z x 0); have hx:Jets.Touch.Seat L (-θ) f:=hS.timesL _
   have hg (E:ℝ→ℝ)(h:Jets.Touch.Seat L (-θ) E):Jets.Touch.Seat L (-θ) (fun x=>degreePrice (radiusB x) (E x) 1):=by
       have hf: Jets.Touch.Seat L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)):=by simpa only [one_mul] using expensed (L:=L) 0 1 0
       unfold degreePrice Trees.stretch; simp only [div_one]; exact (hf.ponies h |>.timesL 4 |>.above (by linarith))
   filter_upwards [hh,(hg t hS).shrinks (by linarith) (show 0<(1/2:ℝ) by norm_num),(hg f hx).shrinks (by linarith) (show 0<(1/2:ℝ) by norm_num),(hS.times ((1-(1/2:ℝ))⁻¹)).shrinks (by linarith) one_pos,(hx.times ((1-(1/2:ℝ))⁻¹)).shrinks (by linarith) one_pos] with x h1 h2 h3 h4 h5 β
   have he':=hw x β; have ht:f x=barley (Z x β):=congr_arg ((1+2*Real.exp 1)*·) he'
   exact ⟨hz,(h x β) ▸ he,he' ▸ h1, he' ▸ (show degreePrice (radiusB x) (apple (Z x 0)) 1 ≤ 1/2 from (le_abs_self _).trans h2),ht ▸ ((le_abs_self _).trans h3),he' ▸ ((le_abs_self _).trans h4),ht ▸ ((le_abs_self _).trans h5)⟩
lemma oversea (L:Side)(θ:ℝ)(hh:Q.rate ≤ -(3/8:ℝ))(he:0<θ)(hm:0<μ)(hz:0 ≤ α)(hp:α+1+1 ≤ Q.exp) : ∀ᶠ x:ℝ in atTop,∀ β:ℝ, Corner Q (radiusB x) (simple Q L μ C θ β x) α ∧ Corner Q (radiusB x) (billsV Q L μ C θ β x) α:=by
   let v:= μ/16
   have hg: Rate su L (-1) (fun x=>Real.exp (-Delay.hatWin su L (μ/2) (1/2) x /4)):=by
       have h:Rate su L (-1) (fun x=> Real.exp (-v * (Delay.fineMonitor su L x ^ (2:ℝ)))):= Rate.monitor_cutoff (by unfold v; positivity) (by norm_num)
       refine h.congr (Eventually.of_forall fun x=>?_); unfold Delay.hatWin; simp only [Real.rpow_two]; unfold v; apply congr_arg; ring
   let F x β := simple Q L μ C θ β x; let K x β := billsV Q L μ C θ β x
   have hw:Jets.Touch.Seat L (-θ) (fun x=> apple (K x 0)):= ((Seat.eliminated hg (by norm_num)).comb (hoist Q L θ hh)|>.times ((1-(1/2:ℝ))⁻¹))
   have hall : ∀ᶠ x:ℝ in atTop,0<apple (F x 0) ∧ apple (F x 0) ≤ apple (K x 0):=by
      filter_upwards [(Work.E09.betaF_growth su L).eventually_ge_atTop 1] with x hx
      obtain ⟨h,hV⟩:= lite Q L θ x (by linarith) (Real.one_le_rpow hx (by norm_num)); exact ⟨mul_pos (add_pos_of_pos_of_nonneg (Real.exp_pos _) h) (show 0< (1-(1/2:ℝ))⁻¹ from by norm_num),mul_le_mul_of_nonneg_right (add_le_add le_rfl hV) (show 0≤ (1-(1/2:ℝ))⁻¹ by norm_num)⟩
   have hx:Jets.Touch.Seat L (-θ) (fun x=> apple (F x 0)):= hw.compares (hall.mono (fun x ⟨h,h'⟩=> (abs_of_pos h).trans_le (h'.trans (le_abs_self _))))
   filter_upwards [framer Q F he hz hp (fun _ _ =>rfl) (fun _ _=>rfl) (hall.mono fun _ h=> h.1) hx, framer Q K he hz hp (fun _ _=>rfl) (fun _ _=>rfl) (hall.mono fun _ h=> h.1.trans_le h.2) hw] with x h h' β using ⟨h β,h' β⟩
end YM.QCD.Loom.Fleet.Glow
#print axioms YM.QCD.Loom.Fleet.Glow.royalties

#print axioms YM.QCD.Loom.Fleet.Glow.oversea
