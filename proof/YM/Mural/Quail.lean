import YM.Mural.Drum
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
-- auxiliary shift from singleton extension
abbrev storm (L:Side)(z:ℝ):ℝ:= (fan L (1/4) z*2)*(↑(Animals.ballCost (18*radiusB z+1))*(romp L+1:ℕ))
noncomputable def drafts (L:Side)(θ x:ℝ):ℝ:= 14*fundsL L θ x
noncomputable def diceV (L:Side)(μ C θ β x:ℝ):= Pipe.unitsP Q L μ β x C (storm L x) (drafts L θ x)
-- justify via fineMonitor.Sequence every AFTER-L spend meets.
lemma toasted (L:Side)(θ:ℝ)(he:0<θ) : ∀ᶠ x in atTop, storm L x ≤ Delay.fineMonitor su L x ∧ 0 ≤ storm L x:=by
    have hg : Jets.Touch.Seat L 0 (fun x=>(Animals.ballCost (18*radiusB x+1):ℝ)):=by
      unfold Animals.ballCost; push_cast; let H:= Jets.Touch.Seat.numbers (L:=L) (1:ℝ); let E:= ((Jets.Touch.Seat.radius (L:=L)).timesL 18).comb H; exact (((E.comb E).comb H).powered 4).above (by simp)
    have hS: Jets.Touch.Seat L (1/4) (storm L):=((Jets.Touch.Seat.keeps.times 2).ponies (hg.times _)|>.above (by linarith : 1/4+0 ≤ (1/4:ℝ)))
    filter_upwards [hS 1 (by norm_num : (1/4:ℝ)< 1)] with x hx; unfold storm at *; have hg: 0<fan L (1/4) x:=fan_pos ..; refine ⟨(le_abs_self _).trans (hx.trans_eq (Real.rpow_one _)),by positivity⟩
lemma wispy (L:Side)(θ:ℝ)(hm:0<μ)(he:0<θ)(hC:0≤C):∀ᶠ x in atTop,∀ β:ℝ,betaF su x L/2 ≤ β → Costs.Buy (diceV Q L μ C θ β x) L Q.halo (radiusB x):=by
   let p x:= Q.goal L x + drafts L θ x
   have hz:Jets.Touch.Seat L (-θ) p:= (Jets.Touch.Seat.eliminated (Rate.power (a:=Q.rate)) Q.stop).comb (Jets.Touch.Seat.keeps.timesL 14)
   have hh: Jets.Touch.Seat L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)):=by simpa only [one_mul] using expensed (L:=L) 0 1 0
   filter_upwards [Buy.quoted su L hm (show (0:ℝ)<1/2 by norm_num) Q.pos Q.bound Q.usable (show 0 ≤ C+1 by linarith) (by norm_num : (1:ℝ)<2) 5 Q.halo, toasted L θ he, (Delay.shift_pos su L),(hz.ponies (hh.timesL 16)).shrinks (by linarith) Q.pos] with x hx hp hs hv β hβ
   have hf: Delay.fineMonitor su L x ≥1:= Real.one_le_exp (sq_nonneg _)
   have hw : 0 ≤ Delay.bill su L x^5:=by have h:= Delay.bill_ge su L x; positivity
   have ha:0 ≤ p x:=by apply add_nonneg (Real.rpow_nonneg hs.le _); unfold drafts; exact mul_nonneg (by norm_num) (fan_pos ..).le
   refine hx.2 _ 1 0 _ _ (by linarith only [hβ]) le_rfl zero_le_one (Real.one_le_exp (by rw [Real.rpow_one]; positivity)) ?_ ha ?_
   · rw [mul_zero,add_zero,Real.rpow_one,add_mul,one_mul,add_mul]; exact add_le_add (le_mul_of_one_le_right (mul_nonneg hC hw) hf) (hp.1.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (Delay.bill_ge ..))))
   exact (le_div_iff₀ (show (0:ℝ)<16*(Animals.ballCost (radiusB x):ℝ) from by have h:=Animals.neighbors_ge (radiusB x); positivity)).mpr ((le_abs_self _).trans hv)
-- retained <= 100 s
lemma spanning (L:Side)(θ:ℝ)(hm:0<μ)(he:0<θ)(hz:0 ≤ α)(hA:α+1+1 ≤ Q.exp) : ∀ᶠ x in atTop, ∀ β:ℝ, let b:=diceV Q L μ C θ β x; 0< apple b ∧ apple b*(1-(1/2:ℝ))⁻¹ ≤ 100* fundsL L θ x ∧ Corner Q (radiusB x) b α:=by
    let v:= μ/16; have hg: Rate su L (-1) (fun x=> Real.exp (-Delay.hatWin su L (μ/2) (1/2) x /4)):=by
       have h: Rate su L (-1) (fun x=> Real.exp (-v*(Delay.fineMonitor su L x ^(2:ℝ)))):= Rate.monitor_cutoff (by unfold v; positivity) (by norm_num)
       refine h.congr (Eventually.of_forall fun x=>?_); unfold Delay.hatWin; simp only [Real.rpow_two]; unfold v; apply congr_arg; ring
    let b x β:=diceV Q L μ C θ β x
    have hx: Jets.Touch.Seat L (-θ) (fun x=> barley (b x 0)):=(((Jets.Touch.Seat.eliminated hg (by norm_num)).comb ((Jets.Touch.Seat.eliminated (show Rate su L _ (Q.goal L) from Rate.power) Q.stop).comb (Jets.Touch.Seat.keeps.timesL 14))).times ((1-1/2:ℝ)⁻¹)).timesL _
    have hy: Jets.Touch.Seat L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)):=by simpa only [one_mul] using expensed (L:=L) 0 1 0
    have hd: Jets.Touch.Seat L (-θ) (fun x=> degreePrice (radiusB x) (barley (b x 0)) 1):=by unfold degreePrice Trees.stretch; simp only [div_one]; exact ((hy.ponies hx).timesL 4|>.above (by linarith))
    filter_upwards [hd.shrinks (by linarith) (show (0:ℝ)<1/2 by norm_num),(hx.times ((1-1/2:ℝ)⁻¹)).shrinks (by linarith) one_pos,Delay.shift_pos su L,(Jets.Touch.Seat.eliminated hg (by norm_num):Jets.Touch.Seat L (-θ-1) _ ) (-θ) (by linarith),(Jets.Touch.Seat.eliminated Rate.power Q.stop : Jets.Touch.Seat L (-θ-1) (Q.goal L)) (-θ) (by linarith)] with x hd hx hβ hw hq β B
    have h1: Q.goal L x ≤ fundsL L θ x:= (le_abs_self _).trans hq; have h3:0<fundsL L θ x:= fan_pos ..; have hh:0<apple B:=by
       refine mul_pos (add_pos_of_pos_of_nonneg (Real.exp_pos _) (show 0≤ Q.goal L x+drafts L θ x from add_nonneg (Real.rpow_nonneg hβ.le _) (mul_nonneg (by norm_num) h3.le))) (show 0<(1-(1/2:ℝ))⁻¹ by norm_num)
    have ht: apple B ≤ (1+1+14:ℝ)*fundsL L θ x*(1-(1/2:ℝ))⁻¹:=by
       apply mul_le_mul_of_nonneg_right _ (by norm_num : 0 ≤ (1-(1/2:ℝ))⁻¹)
       have h2: Real.exp (-Delay.hatWin su L (μ/2) (1/2) x/4)≤ fundsL L θ x:= (le_abs_self _).trans hw
       exact ((add_le_add h2 (add_le_add h1 (le_refl (14*fundsL L θ x)))).trans_eq (by ring))
    have hS : apple B≤ barley B:= le_mul_of_one_le_left hh.le (by have hf:=Real.exp_pos (1:ℝ); linarith)
    have hD: degreePrice (radiusB x) (barley B) 1 ≤1/2:= (le_abs_self _).trans hd
    have hW : barley B*(1-(1/2:ℝ))⁻¹ ≤1:= (le_abs_self _).trans hx
    have hr: degreePrice (radiusB x) (apple B) 1 ≤ degreePrice (radiusB x) (barley B) 1:= by unfold degreePrice Trees.stretch; gcongr
    refine ⟨hh, ?_,⟨hz,hA,hh,hr.trans hD,hD,(mul_le_mul_of_nonneg_right hS (by norm_num:(0:ℝ)≤(1-(1/2:ℝ))⁻¹)).trans hW,hW⟩⟩; norm_num at *; linarith
end YM.QCD.Loom.Fleet.Glow
#print axioms YM.QCD.Loom.Fleet.Glow.spanning

#print axioms YM.QCD.Loom.Fleet.Glow.wispy
