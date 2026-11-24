import YM.QCD.Glass.Water
import YM.QCD.Sq.Axis
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open High PrismT MeasureTheory
open High PrismT MeasureTheory Sq
open Grass
open Lunar Ring0 Stew.Project Sq
variable {Xs :Twin→ Pixel c N}{eK: Twin→ℝ}{Ac:Set Twin}
section uniqueness
variable {Xv Qv : Pixel c N} {U: St c}{Z:ℕ→Atom su 2}{Tt:PathData su}{f: Flavor N}{O:Clip}{O':PlaqAxes}{Ct :ℝ}
lemma lampA (hv:NormG U f Xv P Tt O Z O' q z Ct a u) : Tendsto (Ring0.glow P O' su (Roll Z P Tt O Xv)) (𝓝[>] (0:ℝ)) (𝓝 (a*q)):=by
  have h0:0< z :=hv.run.1; have hG:∀ᶠ w :ℝ in 𝓝[>] (0:ℝ), w∈Set.Ioc 0 z:=( (show ∀ᶠ w:ℝ in 𝓝[>] (0:ℝ),0<w from self_mem_nhdsWithin).and (nhdsWithin_le_nhds (ge_mem_nhds h0)))
  apply Metric.tendsto_nhds.2; intro t hh; have hh' : Tendsto (fun i:ℝ=> Ct*i) (𝓝[>] (0:ℝ)) (𝓝 0):=(Continuous.tendsto' (f:=fun i:ℝ=> Ct*i) (by fun_prop) _ _ (mul_zero _)).mono_left nhdsWithin_le_nhds
  filter_upwards [hG,hh'.eventually_lt_const hh] with i hi hC; exact lt_of_le_of_lt (hv.pulse.fees i hi) hC
lemma toll_earn (U:EvenA c N)(f:Flavor N)(s:ℝ)(j:Bool): tollM j f (wearK c N s U)=s^2*(tollM j f U):=by unfold tollM; rw [grassK,map_smul]; rfl
lemma same_keys (hv:NormG U f (vest c N w₀ Xv) P Tt O Z O' q z Ct a u) (hp: NormG U f (vest c N w₁ Xv) P Tt O Z O' q z Ct d v) (hx:1/4 ≤ unitF true c (U 1)) (he:0< q)(he₀:0<w₀)(he₁:0<w₁): w₀=w₁ ∧ a=d ∧ u=v:=by
   let F:= unitF true c (U 1); let f':= tollM true f (Xv 1)
   have h₁: w₀^2*f'=F:=(toll_earn (Xv 1) f w₀ true).symm.trans hv.lea
   have h₂: w₁^2*f'=F:=(toll_earn (Xv 1) f w₁ true).symm.trans hp.lea
   have hf: 0<f':= pos_of_mul_pos_right (by linarith only [h₁,hx]: 0<w₀^2*f') (sq_nonneg _)
   have h: w₀^2=w₁^2:= mul_right_cancel₀ hf.ne' (h₁.trans h₂.symm)
   have hu: w₀=w₁:=by nlinarith; 
   subst w₁; exact ⟨rfl,mul_right_cancel₀ he.ne' (tendsto_nhds_unique (lampA hv) (lampA hp)),add_left_cancel (hv.life.symm.trans hp.life)⟩
end uniqueness
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.same_keys
