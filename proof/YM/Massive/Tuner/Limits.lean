import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Shoot
import YM.Massive.Pressure.Minor
import YM.Massive.Pressure.Smoothed
import YM.Massive.Tuner.Flat
import YM.Massive.Tuner.Empty
import YM.Massive.Tuner.Budget
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
Bpressure analogue. `K` a lower-margin expense (large positive), `A` majorant size.
uniform over the x (β) tail, *all* k on the M from the initial DomainF, *all* steps
in these positive-common-mass histories. Include actual lower and upper as used in E.
Use `#` exactly: spare = 3 v + 1, rich = 3 v - 3. In particular bounds may be used
without paying a `log(h)` in every volume degree. On passing to the large x gates,
the torus populations can also pay the last few powers when wanting bounds with matched
power `3v`; here state with the displayed actual powers. Never assume the precision
needed to do a stability argument on perturbing the *entire* mass ray has been achieved
just by this positive-common-mass lower.
-/
variable {n0 : ℕ} {B₀ : Side} {J : Patch}
variable (L : HaarBudget su)

local notation "Cₘ" => towerQ O B n i k
set_option quotPrecheck false
structure NormPrices (T:Teller su) (g A K:ℝ) (X:Pixel c N) (z:ℝ):Prop where
   lower : z * Globe.expo K c *
      (L.small*g^su.lieDim * Real.exp (-(T.bind.penalty * 2)))^spare c ≤ (Cvol X).re
   roots U : ‖X U‖ ≤ z * Massive.Pressure.major su c A (2*g/strength T.top.clip) U
   upper : (∫ U,‖X U‖ ∂prior su c) ≤ z * Globe.expo (-A) c *
      (L.big*(2*g/strength T.top.clip)^su.lieDim)^YM.SectorNext.Vacuum.rich c

-- exact use of L2/Frob irrelevant `‖X U‖` the exterior norm, same as in pB.
lemma NormPrices.byRoots (T:Teller su) (X:Pixel c N) (s:ℝ)(he : 1<c.val) (hu:0≤z) (hg:0<s)
    (hL:z * Globe.expo D c * (L.small*s^su.lieDim * Real.exp (-(T.bind.penalty * 2)))^spare c ≤ (Cvol X).re)
    (h:Continuous X) (hT: ∀ V,‖X V‖ ≤ z*Massive.Pressure.major su c A (2*s/strength T.top.clip) V):
    NormPrices L T s A D X z:=by
  refine ⟨hL,hT,?_⟩; let Q:=(2*s/strength T.top.clip); have hq : 0<Q:= div_pos (by positivity) (strength_pos _)
  have hp:=integral_mono (μ:=prior su c) (h.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (((Massive.Pressure.major_cont su c A Q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul z) hT
  rw [integral_const_mul] at hp; refine hp.trans ((mul_le_mul_of_nonneg_left (Massive.Pressure.integral_major L A hq he) hu).trans_eq ?_); unfold Globe.expo; rw [mul_assoc z,neg_mul_neg]

structure Regular (θc : ℝ)(A K₀:ℝ)(T:Teller su)(Q:ConnectedActivityE6.Target su T)(B:SparkMesh)(b:Flavor N)(x κ:ℝ)(τ:Policy Q T.top N)
    (g:PulseRide T.bind T.top.clip O a d S' n)(P':ℕ→BudgetPoint)(X:ℕ→SunR Ω)
    (Y:ℕ→ℝ)(D W':ℝ)(k:ℕ)(V U W:ℕ→ℝ)(A0:∀ i,Pixel (towerQ O B n i k) N) : Prop extends
    Gated θc T B b g P' X Y κ x τ.t D W' k V U W A0 where
  truepath (i:ℕ) (h:i≤n) : ProperF (A0 i)
  flows (i:ℕ) (h:i≤n) : Continuous (A0 i)
  real (i:ℕ) (h:i≤n) : Rain.realP (A0 i)
  solvent (i:ℕ) (h:i≤n) : 0 < (Cvol (A0 i)).re
  leg (i:ℕ) (h:i≤n) : ∃ (F:Voice (towerQ O B n i k) N) (z:ℝ), 0<z ∧
    Enn (P' i) b O.L (delay O n i x) τ.t (1/8) (duo F.P F.K) ∧
    A0 i=z • songBody B F g (P' i) (X i) x (V i) (U i) (k:=k) (i:=i) (T':=T) ∧
    NormPrices L T (gaugeSize O.L (delay O n i x)) A K₀ (A0 i) z
  beta (i:ℕ) (h:i≤n) : 1≤ V i
  mass (i:ℕ) (h:i≤n) : |U i| ≤ 1

-- single-bound tuning preparation hypotheses
variable (Kt A'':ℝ) (Ω : ParcelR) (T : Teller su)
structure Heat (b:Flavor N)(T:Teller su)(O:Patch)(B₀:Side)(A Ωp:ℝ) (P:ParcelR)(κ η x a d s : ℝ) :Prop where
  enough : 2 ≤ run O.L x
  g_pos : 0< gaugeSize O.L x
  g_le : gaugeSize O.L x ≤ 1
  exact_ : run O.L x * gaugeSize O.L x ^ 2=1
  adjacent : run O.L (run O.L x) ≤ 2 * run O.L x
  range_ : roofK O.L η κ x ≤ 1
  fan_ : 1 ≤ fan O.L η x
  chip : |Jets.Touch.chip O.L x|≤1
  high (c : Side) (p : BudgetPoint) (hq : Now O.L p T.top x) (F : Voice c N) (he : Enn p b O.L x η (1/8) (duo F.P F.K)) (v:Train O.J) (E : SunR P) (D:PathData su) (β m:ℝ)
      (hL:D.Bounds T.top.clip a d s) (hm: |m|≤roofK O.L η κ x) (hb:run O.L x/2≤β) (hB:β≤2*run O.L x) (U:Grid c) : ‖red F.P F.K E (passportM O.J O.order_cut) v p D T.top.clip (haloK O.L x) β m 0 U‖ ≤ Massive.Pressure.major su c A (2*gaugeSize O.L x / strength T.top.clip) U
  low (c : Side) (p : BudgetPoint) (F : Voice c N) (he : Enn p b O.L x η (1/8) (duo F.P F.K)) (v:Train O.J) (E : SunR P) (D:PathData su) (β m:ℝ) (hm:|m|≤roofK O.L η κ x) (k:ℕ) (hC:c=B₀*O.L^k) (z:ℝ) (Y: Pixel c N) (hz:0<z) (hY:Y=z • red F.P F.K E (passportM O.J O.order_cut) v p D T.top.clip (haloK O.L x) β m 0) (h:Rain.realP Y) : z*Globe.expo Ωp c ≤ (cBer Y 1).re
  cap : 1+(Fintype.card PlaqAxes:ℝ) ≤ Ωp

-- unify J=4 proofs
lemma heatExists (T) (Ω:ParcelR) (O:Patch) (hO:O.J=4) (hk:0<κ) (hη:0<η) (hh:Ω.Rates σ)
    (hB:Globe.DomainF (passportM 4 le_rfl) N O.L B₀ H) (a d s:ℝ) : ∃ A D:ℝ, ∀ᶠ x in atTop, ∀ y,x ≤ y→ Heat b' T O B₀ A D Ω κ η y a d s:=by
  let J:= O.J; obtain ⟨Z,hU⟩:=unmarked (b':=b') -- args edit
       (passportM O.J O.order_cut) T O.L Ω a d s κ η hh hη hk
  let K := max (1+(Fintype.card PlaqAxes:ℝ)) H
  obtain ⟨r,hr⟩:= eventually_atTop.mp (hU.and ((prices T.top O.L η κ hk hη).and (flatBudget (U:=Ω) b' κ η (passportM 4 le_rfl) hη _ _ hB))) -- args
  refine ⟨Z,K,?_⟩; filter_upwards [eventually_ge_atTop r] with x hx y hy; obtain ⟨hz,⟨ha,hb,hc,hd,he,hf,hg,hH,-⟩,h⟩:=hr _ (hx.trans hy)
  refine ⟨ha,hb,hc,hd,he,hf,hg,hH,fun c p h F he v E D β m hL hm hb hB U=>hz c p h F he U v E D hL β m hb hB hm,?_,le_max_left ..⟩
  intro c p F he v E D β m hm k hC z Y hZ hY hF
  apply le_trans (mul_le_mul_of_nonneg_left (Globe.earns (le_max_right ..)) hZ.le)
  suffices H:∀ (j:ℕ) (hj:4≤j) (hi:j=4) (v: Train j), (Y = z • red F.P F.K E (passportM j hj) v p D T.top.clip (haloK O.L y) β m 0) → _ by exact H _ _ hO _ hY
  intro j hj hi v hv; subst j; simpa only [scent_one,mul_one,Real.exp_zero] using (h k _ hC F p he Y hF T.top.clip E v D β m z hZ hm hv)
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.heatExists
