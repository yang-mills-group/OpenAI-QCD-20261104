import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Shoot
import YM.Massive.Pressure.Minor
import YM.Massive.Pressure.Smoothed
import YM.Massive.Tuner.Flat
import YM.Massive.Tuner.Empty
import YM.Massive.Stiffness.Limit
import YM.Massive.Tuner.Common
import YM.Massive.Reference.Fly
import YM.Massive.Pressure.Major
import YM.QCD.Tide.Palace
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N)
namespace Reference
open Next.Rank IV
variable {s t A'' :ℝ}
open NormedSpace
open MeasureTheory
open YM.SectorNext.Vacuum (rich spare)
open YM.Massive.Pressure (scent_one)


/-!
# Send a cutoff/reference tower on fixed-stride path into an actual Run in the prescribed scheme

Along with all growing-step density/mass estimates on this SAME run before and after blocking.
Existence component, not the desired passage to progressive strides for exact slopes and field
budgets.
-/

open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open YM.Massive.Reading (planeProbe)


-- at this mesh, any sufficiently-large torus supports all calibration checks simultaneously
-- over a given depth. `Signal` check also after a true step, all flavors.
variable {K1 K2 θc : ℝ} (L1:HaarBudget su)
structure FitLevel (τ: Policy Q T'.top N) (B: SparkMesh) (b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n) (A K:ℝ)(P:ℕ→BudgetPoint)(X:ℕ→SunR Ω)(Y:ℕ→ℝ)(κ x D b ε:ℝ) (k : ℕ) : Prop where
    attend (q:ℝ)(V U Wv:ℕ→ℝ)(A0:∀ i,Pixel (towerQ O B n i k) N)
      (h:Regular L1 q A K T' Q B b' x κ τ g P X Y D b k V U Wv A0) (i:ℕ)(hi:i≤n):
      Massive.Stiffness.Window (Cove.light _ ∘ A0 i) (V i) ε ∧
        (0 < i → ∀ f:Flavor N,‖planeProbe (Cove.light _ ∘ A0 i) f- (U i:ℂ)‖ ≤ ε)

variable (hw: O.Branches T'.bind su) (hΩ : Ω.Rates γ)
variable (h0 : ∀ᶠ c:Side in atTop, Signal Ω O.L (passportM O.J O.order_cut) ε κ τ'.t x b' c)
variable (hP : ∀ i,Now O.L (P' i) T'.top (delay O n i x))(hg: Invoice g Q.table V₁ T₁ σ η α D Λ)
include hΩ h0 hP hg
lemma accurate (hε:0< ε) : ∀ᶠ k:ℕ in atTop, FitLevel L1 τ' B b' g K1 K2 P' X Y κ x D W' ε k:=by
   let c i k:=towerQ O B n i k
   let p(i:ℕ) :=P' i
   let v i:=delay O n i x
   let t i:=2*hatG O n i x
   let F i:= Signal Ω O.L (passportM O.J O.order_cut) ε κ τ'.t x b' i
   let W i:= Stiff b' (p i) O.L κ (v i) τ'.t a d Λ (t i) ε T'.top.clip Ω (passportM O.J O.order_cut)
   have h(i:Fin (n+1)):∀ᶠ k in atTop, W i (c i k) ∧ F (c i k):=(show Tendsto (c i.val) atTop atTop from spline (i:=i.val) T' B g p X Y (p:=0) 0 0).eventually ((issue (passportM O.J O.order_cut) b' T'.top.clip (hP i).ball hΩ a d Λ _ _ _ hε (η:=τ'.t)).and h0) -- check hk arguments
   filter_upwards [eventually_all.mpr h] with k hK
   refine ⟨fun q V U Wv A H i hi=>?_⟩; have h:=hK (⟨i,by omega⟩:Fin (n+1)); obtain ⟨F,z,hz,hE,he,-⟩:= H.leg i hi
   refine ⟨(?_ : Massive.Stiffness.Window (Cove.light _ ∘ A i) (V i) ε),?_⟩ -- args
   · have hp': |V i|≤ t i:=by rw [abs_of_nonneg (zero_le_one.trans (H.beta i hi))]; exact (H.costs i hi).1.2
     exact h.1.confirm (g.path i) (X i) (tile O i) F _ z (U i) 0 (V i) hE (hg.he i hi).1 hp' hz _ he
   intro h' f'
   cases i with
   | zero=> omega
   | succ i=> exact (h.2.bounds (v (i+1)) (matters ..) (tile O (i+1)) _ _ (g.path (i+1)) T'.top.clip (p (i+1)) _ _ (U (i+1)) z hz hE (H.costs _ hi).2.2.1 _ he (H.lawT i hi) (H.truepath (i+1) hi)).2 f'
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.accurate
