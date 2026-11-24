import YM.Parishes.Hike
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j kP k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j kP}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open MassiveQCD.Lyre MassiveQCD.Plate MassiveQCD.Lyre.Drawing Massive.Poised.Plans Massive.Poised.Pipes
namespace Bank.Hike
variable (L:Side) (b₀ i0 Kq n Dx nL:ℕ)(θ:ℝ)
local notation "μ⁰"=> (1/8:ℝ)
open QCD.Calm
abbrev FeeE (i Kq n:ℕ)(x:ℝ):= Girdle.tariff i 2 Kq n*Reel.voiceE 2 (1/8) (radiusB x)
noncomputable def ArchC (L:Side)(θ:ℝ)(b i Kq n Dx nL:ℕ)(x:ℝ) := let B:=radiusB x; let C:= FeeE i Kq n x; let Φ₀:=C*King.flowM L x; let Ψ₀:= C*King.jelly L x; Reel.voiceE (Dx*nL) 1 B*(Warmlet.chill b x*Φ₀+Ψ₀)+ (Girdle.price (wiCost B) Kq n Dx nL*crownCost Dx nL B)*(fan L (-θ/4) x*Jets.Touch.chip L x)
-- Seats.Earn rank life and K. 
local notation "F₀"=> ArchC L θ b₀ i0 Kq n Dx nL
lemma prepSignal : Signal L (-θ/4) F₀:=by
    let r:= -θ/4; let t:=(frostQ b₀:ℝ)⁻¹; have ht:0 < t:=by unfold t frostQ; positivity
    have hh: Rate su L (-3) (Warmlet.chill b₀):= ((Rate.cutoff ht).compare (Eventually.of_forall fun x=>?_)); swap
    · unfold Warmlet.chill; change _ ≤|Real.exp (-t*Stores.till x)|; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; exact mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (Nat.div_le_self (radiusB x) _)) (by change -t ≤ 0; linarith)
    let g:=FeeE i0 Kq n; have hg:Rate su L 0 g:= (Reel.for_voices L _ _).mul_left _
    have h₁: Rate su L (-1-1/40) (fun x=> Warmlet.chill b₀ x* (g x*King.flowM L x)+g x* King.jelly L x):= Rate.add ((hh.mul (hg.mul (show Rate su L (-(3/10)) (King.flowM L) from Rate.power))).weaken (by norm_num)) ((hg.mul (show Rate su L (-1-1/40) (King.jelly L) from Rate.power)).weaken (by norm_num)) -- edit
    have hA: Signal L r (fun x=>fan L r x*Jets.Touch.chip L x):=(Jets.Touch.Seat.keeps (L:=L) (a:=r)).equal ( (event_chip L 1).mono (fun i hi=> by change _*_=fan L _ _; rw [mul_assoc,mul_inv_cancel₀ hi.2.1.ne',mul_one]))
    let W(x:ℝ):=(wiCost (radiusB x):ℝ)
    have hW:Jets.Touch.Seat L 0 W:=by unfold W wiCost; push_cast; have hR:Jets.Touch.Seat L 0 (fun x=>(radiusB x:ℝ)):=Jets.Touch.Seat.radius; exact (((hR.ponies ((hR.timesL 4).comb (Jets.Touch.Seat.numbers 2))).above (by linarith)).comb (hR.timesL 2))
    have hv(u:ℝ→ℝ)(k:ℕ)(hp:Jets.Touch.Seat L 0 u):Jets.Touch.Seat L 0 (fun x=> u x^k):= (hp.powered k).above (by simp)
    have hw(f g:ℝ→ℝ)(hf:Jets.Touch.Seat L 0 f)(hg:Jets.Touch.Seat L 0 g): Jets.Touch.Seat L 0 (fun x=>f x*g x):= (hf.ponies hg).above (by simp)
    have hG(i:ℕ): Jets.Touch.Seat L 0 (fun x=>Girdle.shift (wiCost (radiusB x)) i):= hv _ _ ((Jets.Touch.Seat.numbers 1).comb hW)
    unfold ArchC; apply Signal.palms; exact Signal.seed ((Reel.for_voices L (Dx*nL) 1).mul h₁) (by linarith); apply Signal.pay hA; exact hw _ _ ((hw _ _ (hv _ _ (hG Kq)) (hG 2)).comb (hw _ _ (hv _ _ (hG Kq)) (hv _ _ (hG Dx)))) (hv _ _ (hG Dx))
lemma hung (M:ℝ)(h:0<M)(he:0<θ):∀ᶠ x in atTop, F₀ x ≤ M*Jets.Touch.chip L x:= Signal.moneyP (prepSignal L b₀ i0 Kq n Dx nL θ) (by linarith) h
end Bank.Hike
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Bank.Hike.hung
