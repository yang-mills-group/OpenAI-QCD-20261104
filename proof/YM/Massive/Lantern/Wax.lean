import YM.QCD.Cabin.Reach
/-! Startup K spare. `Pencil` constructor holds also with per-flag quote 8*; adapted from Reach. -/
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
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ ψ t:ℝ} {U V:SunR Ω} (P₀:Plan j) (Θ:ℝ)
open WilsonStartup.Start WilsonStartup.Padded Progress.DirectedRecipe Ovens
variable (L G)
lemma excessBirth (N:ℕ)(hk:G.clip.direct≤1):∀ᶠ x in atTop,∀ P:BudgetPoint, Now L P G x→∀ β, betaF su x L/2 ≤ β → β ≤2*betaF su x L→∀ c:Side,Quits (birthV c P N G.clip β).K P.B 1 (taxK L x 8) 1 (fan L Θ x):=by
   have hp:=Work.E09.betaF_growth su L; have hg:= Real.tendsto_log_atTop.comp hp
   filter_upwards [Jets.Touch.Seat.your L|>.eventually_ge_atTop 512,framesC L 1 zero_lt_one,hp.eventually_ge_atTop 1,hg.eventually (WilsonStartup.Timing.loan G.supportExponent),hp.eventually (plusT G hk),hg.eventually (Timing.shrinking.eventually (ge_mem_nhds (Start.constants su G.order G.power).2.1)),hg.eventually (Timing.afford su G)] with x hR hφ hf hL hX hh hY P hP β hβ h c
   let t:= betaF su x L; let z:=Real.log t; have ht:= zero_lt_one.trans_le hf; have hz:0≤z:= Real.log_nonneg hf
   have hQ:= Time.threshold_aligned t ht; have hT:P.threshold=Pressure.temp t:= hP.baseG; have hW:P.threshold=Timing.temp z:= hT.trans (hQ.1.symm.trans hQ.2.symm)
   obtain ⟨hD,-⟩:= hL P hW hP.ball hP.era.2.2; change Loan P (Real.exp z /2) (Timing.M z) (Timing.M z) (Timing.quota z) at hD; rw [show Real.exp z=t from Real.exp_log ht] at hD
   have hxP:= (hX P hP.era.2.2.symm hP.ball hT).1
   have hδ :1 ≤ pra L x:=by simpa only [fan,Real.rpow_one] using hφ.2.1
   have h' :0≤β:= by linarith
   have hx : Timing.normE z ≤ Jets.Touch.chip L x:= by
         calc
           Timing.normE z ≤ Real.exp (-z):=Real.exp_monotone (by linarith)
           _ ≤ _:=by unfold Jets.Touch.chip; rw [Real.exp_neg,show Real.exp z=t from Real.exp_log ht]; exact le_mul_of_one_le_right (inv_pos.mpr ht).le hδ
   have hm:pra L x=Timing.M z:=rfl; have hs' : G.order≥4:=by linarith [G.order_ge]
   let p:=pra L x; apply trimV N c G.clip β P hxP hD hβ (fan_pos ..) (show 1≤ P.supportExponent+1 from (by linarith [P.exponent_pos])) (Real.exp_pos _|>.le); rw [← hm]; apply Real.exp_monotone
   let y:=p^(1/3:ℝ); have hL:8 ≤ y:=by
      have ht:8=(512:ℝ)^(1/3:ℝ):=by rw [show (512:ℝ)=(8:ℝ)^(3:ℝ) from (by norm_num),← Real.rpow_mul (by norm_num)]; norm_num
      exact ht.trans_le (Real.rpow_le_rpow (by norm_num) hR (by norm_num))
   have he: y*y*y=p:=by unfold y; have hp:p≥0:= (zero_le_one.trans hδ); rw [← Real.rpow_add (zero_lt_one.trans_le hδ), ← Real.rpow_add (zero_lt_one.trans_le hδ)]; norm_num;rfl
   change 8*y≤p; rw [← he]; nlinarith
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.excessBirth
