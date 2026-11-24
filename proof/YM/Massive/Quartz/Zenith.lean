import YM.Massive.Quartz.Read
import YM.Massive.Stiffness.Limit
/-! # Window post-β p needed. Gauge tests with unchanged stencil counts. Only after n, x: call k. From `Stiffness/Limit.lean`. -/
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
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ C w₁ w₂ W:ℝ}
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
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
open Nola Sway OrbitG NormedSpace Creek Grove MeasureTheory
namespace Reference
variable {z a' θ:ℝ}
open YM.Massive (Stiffness.body Stiffness.action)
open YM.Pert
open YM.Massive.Stiffness (fullLog classicalPath)

variable (Fv: Voice c N) (X0:Pixel c N) (E : SunR Ω) (v:Train j) (D' : PathData su) (Bv : Clip)
variable (hp : Enn P b' L x η (1/8) (duo Fv.P Fv.K))
variable (hk : P.B = highR L x)
variable (he : X0 = u • red Fv.P Fv.K E P₀ v P D' Bv θ β b 0)
variable (hD : D'.Bounds Bv σ C Λ) (hΩ : Ω.Rates γ)
open YM.Massive.Stiffness (papyrus)
open YM.Pert.Kinetic
open Filter

structure TicketW (N:ℕ) (t:BudgetPoint) (θ δ σ C Λ W ε:ℝ) (B:Clip)(X:ParcelR) (P:Plan j) (c:Side) : Prop where
    confirm (D : PathData su)(U:SunR X)(P':Train j)(F:Voice c N)(v:ℝ)(k u y b:ℝ)
      (h: CrossP F.P)(hz:Licence t (1/8) δ θ F.P)(hv : D.Bounds B σ C Λ) (hb: |b|≤W)(hk:0<k)(A:Pixel c N)
      (hA:A=k • red F.P F.K U P P' t D B v b u 0):
      Massive.Stiffness.Window (Cove.light _ ∘ A) b ε


include hΩ
set_option maxHeartbeats 400000 in
theorem hold (σ C Λ W ε ρ δ:ℝ) (hρ:0<ρ)(he :0<ε)(hp₂:2*(3/P.threshold^2)*δ ≤ε/2) : ∀ᶠ c:Side in atTop, TicketW N P ρ δ σ C Λ W ε Bv Ω P₀ c:=by
   let z := runningCost Ω σ C Λ W δ N P
   let k (s:ℝ) := z*s+W*|(Real.sinc (s/2))^2-1|
   have h : Tendsto Full.mesh atTop (𝓝 0):= by
         change Tendsto (fun i:Side=> (2*Real.pi:ℝ)/ Globe.HalfMass.amount i) atTop (𝓝 0); simp_rw [div_eq_mul_inv]; simpa only [mul_zero, Function.comp_apply] using (tendsto_inv_atTop_zero.comp Massive.Reading.large).const_mul (2*Real.pi)
   have hp: Tendsto k (𝓝 0) (𝓝 0) := (show Continuous k from (by unfold k; fun_prop (disch:=apply Real.continuous_sinc))).tendsto' 0 0 (by simp [k,Real.sinc_zero])
   filter_upwards [(hp.comp h).eventually_le_const (half_pos he),eventually_ge_atTop (⟨4,by decide⟩:Side)] with c hc hM; refine ⟨fun D U P' F v a u y b H hz hD hb ha A hA=>?_⟩
   have hn:4 ≤ c.val:= hM
   have h(j:Bool)(i l:Axis)(T:su.Color): ContDiffAt ℝ 2 (Massive.Stiffness.action (Cove.light _ ∘ A) ∘ Massive.Stiffness.profile (trig j) i l T) 0:=by rw [profile_eq T j i l hn]; exact (actionM _ _ _ _ _ _ _ H hρ hz hA hD hΩ ha hn _).1
   refine ⟨arm_m _ _ _ _ _ _ _ H hρ hz hA ha,fun i j h' g=>⟨h false i j g,h true i j g⟩,fun i j h' g hg=>?_⟩
   have he:= calibrating_m _ _ _ _ _ _ _ H hρ hz hA hD hΩ ha hn g hg i j h'; let m:=Full.mesh c; let f:= b*Real.sinc (m/2)^2; let T:= Massive.Stiffness.read (Cove.light _ ∘ A) i j g; change |T-b| ≤_; change k m ≤ ε/2 at hc
   rw [show T-b= (T-f)+ b*(Real.sinc (m/2)^2-1) from (by unfold f; ring)]; apply (abs_add_le ..).trans; have h : 0 < m:=Full.mesh_pos; rw [abs_mul]
   let A:=runningCost Ω σ C Λ b δ N P; have H : |T-f| ≤ z*m + ε/2:= le_trans (show _ ≤ A*m + 2*(3/P.threshold^2)*δ from he) (add_le_add (mul_le_mul_of_nonneg_right (slower b hb hD.width) h.le) hp₂); unfold k at hc; linarith only [H,hc,mul_le_mul_of_nonneg_right hb (abs_nonneg (Real.sinc (m/2)^2-1))]
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.hold
