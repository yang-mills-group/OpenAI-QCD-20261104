import YM.QCD.Loom.Gale
import YM.QCD.Loom.Volt
/-! # tickets across stage line -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R :Rep su f}{s : Ratio c f}
variable {H:Cash W τ μ L Q o C T R}{N m l n:ℕ}
-- budgets q implied from Telly
-- powers

def shiftCost (L:Side)(x:ℝ) (m:ℕ):ℝ:= fan L (1/4) x*((Animals.ballCost (18*radiusB x+1):ℝ)*m)
def bootstrut (L:Side)(θ x:ℝ) :ℝ:= (cashM L θ x)⁻¹*(fan L (-θ-θ/2) x*(1-fan L (-θ) x)⁻¹)
def demandQ (L:Side)(θ x:ℝ):= bootstrut L θ x + (betaF su x L ^ (-(3/8):ℝ) + betaF su x L ^ (-(3/8):ℝ))
def romp (L:Side):ℕ:= (L.val^4+1)+1
lemma taken (L:Side)(i:ℕ):∀ᶠ x in atTop,shiftCost L x i≤Delay.fineMonitor su L x:=by
   have hg : Jets.Touch.Seat L 0 (fun x=>(Animals.ballCost (18*radiusB x+1):ℝ)):=by
      unfold Animals.ballCost; push_cast; let H:= Jets.Touch.Seat.numbers (L:=L) (1:ℝ); let E:= ((Jets.Touch.Seat.radius (L:=L)).timesL 18).comb H; exact (((E.comb E).comb H).powered 4).above (by simp)
   filter_upwards [ ((Jets.Touch.Seat.keeps (a:=1/4)).ponies (hg.times i)) 1 (by norm_num)] with x hx; exact (le_abs_self _).trans (hx.trans_eq (Real.rpow_one _))
lemma cunning (L:Side)(θ:ℝ)(he:0<θ):
   Rate su L (-(3/8)) (demandQ L θ) ∧ ∀ᶠ x in atTop,0<demandQ L θ x:=by
    have he' := Jets.Touch.Seat.shrinks (f:=fan L (-θ)) Jets.Touch.Seat.keeps (by linarith) (show 0<(1/2:ℝ) by norm_num)
    constructor
    · have hf:Rate su L 0 (fun i => (1-fan L (-θ) i)⁻¹):=by
         apply Rate.compare (Rate.const 2); filter_upwards [he'] with x hx
         have hg:fan L (-θ) x ≤1/2:=(le_abs_self _).trans hx; have hp: 1/2 ≤1-fan L (-θ) x:=by linarith
         have ht:0 < (1/2:ℝ):=by norm_num
         exact (abs_of_pos (inv_pos.mpr (ht.trans_le hp))).trans_le ((inv_anti₀ ht hp).trans (by norm_num))
      exact Rate.add (((cash_h L θ).mul ((Jets.Touch.Seat.ruled (f:=fan L (-θ-θ/2)) Jets.Touch.Seat.keeps).mul hf)).weaken (by norm_num)) (Rate.power.add Rate.power)
    filter_upwards [Delay.shift_pos su L,event_chip L θ,he'] with x hx hg hX
    have hp:0 < bootstrut L θ x:=mul_pos (inv_pos.mpr (by have h:=hg.2.2.2; linarith)) (mul_pos (fan_pos ..) (inv_pos.mpr (by linarith [(le_abs_self _).trans hX])))
    exact add_pos_of_pos_of_nonneg hp (by positivity)
lemma guests (Q:Target su P)(L:Side){μ θ C:ℝ}(hμ:0<μ)(ht:0<θ)(hC:0≤ C):∀ᶠ x:ℝ in atTop,∀ β:ℝ, betaF su x L/2≤β →(Pipe.unitsP Q L μ β x C (shiftCost L x (romp L)) (demandQ L θ x)).Buy L Q.halo (radiusB x):=by
   obtain ⟨h,hB⟩:= cunning L θ ht
   filter_upwards [h (-(1/4)) (by norm_num),hB, Pipe.subsidy Q L hμ hC one_pos (by norm_num : -(1/4:ℝ)<0),taken L (romp L)] with x H hp hv he
   exact fun b hh=> hv b _ _ hh hp.le ((le_abs_self _).trans H) (he.trans_eq (one_mul _).symm)
end YM.QCD.Loom
