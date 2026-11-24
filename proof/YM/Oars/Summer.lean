import YM.Oars.Pigments
import YM.Oars.Prelude
/-!
 # Local booths in actual clock line.Earn.Frame scaling Verity
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Sail
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {c f L:Side}{β τ :ℝ}
variable {I E J G Gv:Type}[Fintype I][Fintype J]
open Sail Kites Plate.Card QCD.Calm Acre Rails.Reference Rails
open QCD.Acre.Rails.Bank QCD.Acre.Rails.Bank.Hike Stags
open MassiveQCD.Twist
local notation "iC"=> (42/256:ℝ)
local notation "i₀"=> (46/256:ℝ)
local notation "k₀"=> (1/256:ℝ)
local notation "W₀"=> (1/8:ℝ)
local notation "Ω₀"=> (3/16+1:ℝ)
local notation "G!"=> (40/256:ℝ)
variable (L:Side)(θ p u r:ℝ)(k q K η Gn :ℕ)
-- Timing.Shedule using v in monotone transformations pAr.
noncomputable def roomAt (x:ℝ):ℝ:= fan L (-θ/16) x * Jets.Touch.chip L x
noncomputable def tallyUp (i M n:ℕ)(x:ℝ):ℝ:= let s:=run L x; Girdle.tariff i 2 M n*(Real.exp (-(W₀/128)*radiusB s)*(Reel.voiceE 2 W₀ (radiusB s)*King.flowM L s))
-- declare Vol.Incoming feasible for Book with normalized polar W. outgoing after.Any.O.Scope.
lemma bumped (B:ℕ)(t:ℝ) : Jets.Touch.Seat L 0 (fun x:ℝ=> bonus B (radiusB x) t) :=by
   unfold bonus Footprint.payment Footprint.degreeIncome
   let v(x:ℝ):=Footprint.spread 1 (4*radiusB x+4)
   have hv: Jets.Touch.Seat L 0 (fun x=>(Footprint.spread 1 (4*radiusB x+4):ℝ)):=by
       unfold Footprint.spread; simp only [one_mul]; apply QCD.Calm.squares; unfold Strip; push_cast; exact Jets.Touch.Seat.radius.timesL 4|>.comb (Jets.Touch.Seat.numbers _)
   exact ((hv.timesL _|>.times _).times _)
-- needed at highR.Its own cost stalls high ring.Ap.E.Ph. compare highR to monitor.BaseP.Squ. `Seats.radius L` at τ; upper ≤ 2*...
lemma bumpedH (B:ℕ)(t:ℝ): Jets.Touch.Seat L 0 (fun x=> bonus B (highR L x) t):=by
   unfold bonus Footprint.payment Footprint.degreeIncome
   have hv: Jets.Touch.Seat L 0 (fun x=>(Footprint.spread 1 (4*highR L x+4):ℝ)):=by
       have hp: Jets.Touch.Seat L 0 (fun x=>(highR L x:ℝ)):=by
           intro b hb; filter_upwards [Delay.monitor_pays su L 1 (D:=1) zero_le_one hb] with x hx; refine le_trans ?_ hx; unfold highR radiusB Delay.bill; rw [abs_of_nonneg (by positivity),one_mul,pow_one]; have h := Nat.ceil_lt_add_one (sq_nonneg (Real.log (betaF su x L))); linarith only [h,Nat.cast_nonneg (α:=ℝ) (Nat.ceil (Real.log x ^2))]
       unfold Footprint.spread; simp only [one_mul]; apply QCD.Calm.squares; unfold QCD.Calm.Strip; push_cast; exact Jets.Touch.Seat.comb (hp.timesL 4) (Jets.Touch.Seat.numbers _)
   exact ((hv.timesL _|>.times _).times _)
-- projection ticket.In:w P sample geometry charges.OUT K margin
local notation "Rq"=>roomAt L θ
lemma harvestIn (V:ℝ)(hθ:0<θ)(H:ℕ)(hV:0≤V):∀ᶠ x in atTop, bonus H (highR L x) (1/32)*(Rq x*V)+Rq x ≤ spareCut (Jets.Touch.chip L x):=by
     -- Seat.bonus.P v.
     unfold roomAt; let f:= fun i:ℝ=>bonus H (highR L i) (1/32); let s:= -θ/16; have ht:s<0:=by unfold s; linarith
     let Ω:=fun x=> fan L s x; have h: Jets.Touch.Seat L s Ω:= Jets.Touch.Seat.keeps
     have hΩ: Jets.Touch.Seat L s (fun x=> f x*Ω x*V+Ω x):= (Jets.Touch.Seat.ponies (bumpedH L H (1/32)) h|>.times V|>.above (le_of_eq (zero_add _))).comb h
     have hz:0 < spareCut 1:= by unfold spareCut; rw [mul_one,sub_pos]; exact Real.exp_lt_one_iff.mpr (by norm_num)
     filter_upwards [hΩ.shrinks ht hz,event_chip L 1] with x hx hf; let Z:= Jets.Touch.chip L x; have he:=mul_le_mul_of_nonneg_right ((le_abs_self _).trans hx) hf.2.1.le; unfold spareCut at he ⊢; change f x*(Ω x*Z*V)+Ω x*Z ≤ _; linarith only [he]
end YM.MassiveQCD.Sample.Sail
