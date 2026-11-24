import YM.Massive.Mass.Terminal
import YM.Massive.Stiffness.Effective
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
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
lemma profile_eq (T:su.Color) (k: Bool) (i j: Axis) (hn:4 ≤ c.val):
    Massive.Stiffness.profile (trig k) i j T= (AnalyticBridge.VerifiedReset.line (n:=c) (testWave T k i j)) := by
   funext t x; unfold Massive.Stiffness.profile
   have he (y:Site c) : mode j k y = trig k (Massive.Stiffness.waveNumber c*((y j).val:ℝ)):= by
       let x : Cover := Flume.rep y; have hx:wrap c x=y:=Flume.rep_eq y -- grep
       conv_lhs=> rhs; rw [←hx]; -- maybe wrong
       rw [Kinetic.mode_wrap hn]; unfold x Flume.rep; push_cast; rfl
   unfold testWave Kinetic.wave AnalyticBridge.VerifiedReset.line increment; by_cases hi : x.2=i <;> simp [hi, Ne.symm,he, smul_smul]
include he hp
variable (hx:0<u)
include hx
open scoped ComplexOrder in
lemma window_real : ∀ᶠ U in 𝓝 (1:Grid c), 0 < Massive.Stiffness.body (Cove.light _ ∘ X0) U:=by
   have h : (1: Grid c)∈Boulevard.sunny P:=fun i=> by rw [WilsonStartup.face_one,su.chord_one]; exact P.threshold_pos
   filter_upwards [(Boulevard.sky P).mem_nhds h] with i hi; rw [intensity _ _ _ _ _ _ _ _ hp he (Boulevard.smoky hi), ←Complex.ofReal_mul, ←Complex.ofReal_zero, Complex.real_lt_real]; exact mul_pos hx (Real.exp_pos _)

include hk hD hΩ
variable (hn:4 ≤ c.val)
include hn
lemma actionTest (w : Directions su c) :
    let r:= papyrus D' E.Z.page; let Y:= AnalyticBridge.VerifiedReset.line w;
    let f:= Massive.Stiffness.action (Cove.light _ ∘ X0) ∘ Y
    ContDiffAt ℝ 2 f 0 ∧ iteratedDeriv 2 f 0=2*actualPath (p:=Bv) D' β w+N*(2*actualPath (p:=Bv) r 0 w)+iteratedDeriv 2 (correction Fv ∘ Y) 0:=by
   intro r Y f
   let T:= classicalPath Bv D' β ∘ Y; let g:= Extra.Iteration.action E.Z.page ∘ Y; let W:= correction Fv ∘ Y; let K(t:ℝ) := -Real.log u; let J(t:ℝ):ℝ:= N*g t; let Z:= K+T+J+W
   have he' : f=ᶠ[𝓝 0] Z:=by
       filter_upwards [Pert.Kinetic.rays_free P.threshold P.threshold_pos w] with t ht; exact negative _ _ _ _ _ _ _ _ hp he hx ht
   have hpP:= Massive.Stiffness.lineImpact hD w β; have hv:= hΩ.ht; obtain ⟨hd,hx'⟩:= E.Z.permit hv; have hg := Massive.Stiffness.era hD E.Z.page (E.Z.cost hv) hv hd hx' w; let z:= AnalyticBridge.VerifiedReset.spike su; -- exists
   have hW:ContDiffAt ℝ 2 W 0:= (pay b' Fv hp hk z (by exact spike_norm simple) hn true 0 0).2 w
   have hK:ContDiffAt ℝ 2 (K+T) 0:= contDiffAt_const.add hpP.1
   have hJ:ContDiffAt ℝ 2 J 0:= contDiffAt_const.mul hg.1
   have hZ : ContDiffAt ℝ 2 Z 0:=(hK.add hJ).add hW;
   refine ⟨hZ.congr_of_eventuallyEq he',?_⟩; unfold Z at he'; -- no at * hx?
   rw [he'.iteratedDeriv_eq, iteratedDeriv_add (f:=K+T+J) (g:=W) (hK.add hJ) hW, iteratedDeriv_add hK hJ, iteratedDeriv_add (f:=K) (g:=T) (by unfold K; fun_prop) hpP.1]
   rw [show iteratedDeriv 2 J 0= N* iteratedDeriv 2 g 0 from iteratedDeriv_const_mul _ hg.1]; rw [show iteratedDeriv 2 K 0=0 from ?_, zero_add, show iteratedDeriv 2 T 0= _ from hpP.2, show iteratedDeriv 2 g 0= _ from hg.2]
   unfold K; rw [iteratedDeriv_const]; rfl

def runningCost (T:ParcelR)(σ C Λ β δ : ℝ)(N:ℕ)(P:BudgetPoint) : ℝ :=
    2*windPrice σ C Λ β + N * (2*windPrice (min T.t σ) C (Smoke.expPrice 2 T.t*T.e) 0)+2*geomE (℘ P)*δ

lemma calibrating (t:su.Color)(ht: ‖t‖=1)(i j':Axis)(hij:i≠j') :
    let f:= Massive.Stiffness.read (Cove.light _ ∘ X0) i j' t; let m:=Full.mesh c; let D:=runningCost Ω σ C Λ β (Jets.Touch.chip L x) N P
    |f-β * Real.sinc (m/2)^2| ≤ D*m:=by
   intro f m D
   let q : ℝ:= Fintype.card (Site c); have hq:0<q:=by unfold q; positivity; -- maybe Ferm
   let d:= Real.sinc (m/2); have hm:0 < m:= Full.mesh_pos
   have h : 4*Real.sin (m/2)^2= d^2*m^2:=by unfold d; rw [Real.sinc_of_ne_zero (half_pos hm).ne']; field_simp; ring
   let w(k):Directions su c:=testWave t k i j'; let g(k):=actualPath (p:=Bv) D' β (w k); let r:=papyrus D' E.Z.page; let l(k):= actualPath (p:=Bv) r 0 (w k); let W(k):= iteratedDeriv 2 (correction Fv ∘ AnalyticBridge.VerifiedReset.line (w k)) 0
   let a:=windPrice σ C Λ β; let e:=windPrice (min Ω.t σ) C (Smoke.expPrice 2 Ω.t*Ω.e) 0; let A:=geomE (℘ P); let b:= Jets.Touch.chip L x
   obtain ⟨hh,hp'⟩:= E.Z.permit hΩ.ht; have H0:= Massive.Stiffness.ornament_cost _ E.Z.page hD (E.Z.cost hΩ.ht) hΩ.ht hh hp';
   have hV:= Massive.Stiffness.all_rates hD hn i j' hij ht β
   have he':= Massive.Stiffness.all_rates H0 hn i j' hij ht 0
   change |(∑ i':Bool, g i') - _ * _| ≤ q * m^3 * a at hV; rw [h] at hV; change |_ - _| ≤ q * m^3 * e at he'; norm_num only [zero_div,zero_mul,sub_zero] at he'
   have he': |(∑ i:Bool,l i)| ≤ _:= he'
   have hW i:|W i|≤ q*(m^3*A*b):=(pay b' Fv hp hk t ht hn i _ _).1
   have hb(k) : iteratedDeriv 2 (Massive.Stiffness.action (Cove.light _ ∘ X0) ∘ Massive.Stiffness.profile (trig k) i j' t) 0= (2*g k+N*(2*l k))+W k:= by rw [profile_eq t k i j' hn]; exact (actionTest _ _ _ _ _ _ _ _ hp hk he hD hΩ hx hn (w k)).2
   rw [Fintype.sum_bool] at hV he'
   have hp : f*(q*m^2)= (2*g false+N*(2*l false))+W false + ((2*g true+N*(2*l true))+W true):=by unfold f Massive.Stiffness.read; rw [←hb true,←hb false]; exact div_mul_cancel₀ _ (by positivity : q*m^2 ≠0)
   obtain ⟨h1,h2⟩:= abs_le.mp hV; obtain ⟨h3,h4⟩:= abs_le.mp he'; have h5:= abs_le.mp (hW true); have h6:=abs_le.mp (hW false); change |f-β*d^2| ≤ _; have hd : D=2*a+N*(2*e)+2*A*b:=rfl
   apply le_of_mul_le_mul_right _ (by positivity : 0< q*m^2); rw [← abs_of_pos (a:=q*m^2) (by positivity), ← abs_mul]; -- updates both
   rw [abs_of_pos (a:=q*m^2) (by positivity),hd]; apply abs_le.mpr; constructor <;> linarith only [h1,h2,h5.1,h5.2,h6.1,h6.2,mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg N (α:=ℝ)),mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg N (α:=ℝ)),hp]
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.calibrating
