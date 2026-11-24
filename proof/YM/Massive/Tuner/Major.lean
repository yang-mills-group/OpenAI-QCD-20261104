import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Halo
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
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
namespace Reference
open Next.Rank IV
variable {s t A'' :ℝ}
open NormedSpace
abbrev gaugeSize (L : Side) (x : ℝ) := (Real.sqrt (run L x))⁻¹

-- uniform in x all the way to UV, not just on one shell.
lemma prices (t : Stage) (L : Side) (η κ : ℝ) (hκ : 0 < κ) (hη:0 < η) :
    ∀ᶠ x in atTop, 2 ≤ run L x ∧ 0 < gaugeSize L x ∧ gaugeSize L x ≤ 1 ∧
      run L x * gaugeSize L x ^ 2=1 ∧ run L (run L x) ≤ 2 * run L x ∧
      roofK L η κ x ≤ 1 ∧ 1 ≤ fan L η x ∧ |Jets.Touch.chip L x|≤1 ∧
      0 < haloK L x ∧ haloK L x ≤ 1 ∧ ∀ p : BudgetPoint, Now L p t x →
      2*gaugeSize L x ≤ p.threshold ∧ ∀ β, run L x/2 ≤ β → β ≤ 2*run L x → 1 ≤ β * (2*gaugeSize L x)^2 ∧
       (∀ d Λ : ℝ,0 ≤ d → 0 ≤ Λ → PathData.loopsPrice p β d Λ ≤ 4*d+Λ) :=by
    let b := run L
    have ht : Tendsto b atTop atTop:=Work.E09.betaF_growth su L
    filter_upwards [turf L η κ hκ,eventually_ge_atTop (0:ℝ),ht.eventually_ge_atTop 2,summerR L η hη,
      (Jets.Touch.Seat.your L).eventually_ge_atTop 2, event_chip L η,ht.eventually Vac.Numbers.uniform_loop] with x h1 h2 h3 h4 h5 h6 h7
    have h : 2 ≤ run L x:=h3
    let g := gaugeSize L x
    have hg : 0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
    have hj := h4 x le_rfl
    have hh : (Real.sqrt (run L x))^2 = run L x:=Real.sq_sqrt (by linarith)
    have hx : run L x * g^2=1:=by unfold g gaugeSize; field_simp; exact hh.symm
    refine ⟨h,hg,(by change g≤1; nlinarith),hx,(by unfold run betaF; linarith only [h2]),h1.2.1,hj.1, (abs_of_nonneg h6.2.1.le).le.trans h6.2.2.1,hj.2.well,hj.2.yaw,fun p hp=>?_⟩
    have he : p.threshold=Vac.Numbers.theta (run L x):=hp.baseG
    refine ⟨(by rw [he]; change 2*g ≤ g*Vac.Numbers.P (run L x); linarith only [mul_le_mul_of_nonneg_left (show 2 ≤ Vac.Numbers.P (run L x) from h5) hg.le]),?_⟩
    intro β hβ hB
    change 1 ≤ β*(2*g)^2 ∧ _
    refine ⟨(by linarith only [mul_le_mul_of_nonneg_right hβ (sq_nonneg g),hx]),?_⟩
    intro d Λ hd hΛ
    unfold PathData.loopsPrice; apply add_le_add
    · have h':=p.threshold_pos; have h1:run L x * p.threshold^3 ≤1:=by rw [he]; exact h7.2.1
      have h2:run L x*p.threshold^4 ≤1:=by rw [he]; exact h7.2.2.1
      apply (mul_le_mul_of_nonneg_right hB (show 0 ≤ d*p.threshold^3+d*p.threshold^4 by positivity)).trans _ -- arg
      linarith only [mul_le_mul_of_nonneg_left h1 hd,mul_le_mul_of_nonneg_left h2 hd]
    exact mul_le_of_le_one_right hΛ (pow_le_one₀ p.threshold_pos.le p.threshold_le)

section price
-- d,Λ invoice bound; nonpositive d/Λ implies absurd from path. could abs-max.
variable (P : Plan j) (T : Teller su) (L : Side) (Ω : ParcelR) (a d Λ κ η : ℝ)
variable (historyT : Ω.Rates σ)
include historyT
/-- Uniform weak estimate of the *actual*, naked expansion. Consequently for absolute
price upper don't use any positivity of a gauge measure. -/
theorem unmarked (hη : 0 < η) (hκ : 0 < κ) : ∃ K:ℝ,
    ∀ᶠ x in atTop, ∀ (c : Side) (p : BudgetPoint), Now L p T.top x → ∀ (F : Voice c N),
    Enn p b' L x η (1/8) (duo F.P F.K) → ∀ (V : Grid c) (v : Train j) (S : SunR Ω) (D : PathData su),
    D.Bounds T.top.clip a d Λ → ∀ β m:ℝ, run L x/2 ≤ β → β ≤ 2*run L x → |m|≤roofK L η κ x →
    ‖red F.P F.K S P v p D T.top.clip (haloK L x) β m 0 V‖ ≤
      YM.Massive.Pressure.major su c K (2*gaugeSize L x/strength T.top.clip) V:=by
   obtain ⟨M,hM⟩:= Globe.uniformVeil P Ω historyT 1
   let e := 2^2 * (Smoke.expPrice 2 Ω.t*Ω.e)
   let W := Globe.bPeak M N + (↑N*e + 4*d + Λ + Fintype.card PlaqAxes)
   refine ⟨W+2,?_⟩
   filter_upwards [prices T.top L η κ hκ hη] with x hx c p hp F hF V v S D hD β m hβ hB hm
   obtain ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,t⟩:= hx
   let A := scent S.Z.page p D T.top.clip β 0 N V
   let D' := FieldB Ω S c (haloK L x) P v + m • 1
   let X : EvenA c N := nozzle c N (D' V); let Y:= Patron.total F.P p.threshold V
   have ht:= (t p hp); let l : ℝ := Fintype.card (Site c); let O:= (2*gaugeSize L x/strength T.top.clip)
   let R:=∑ u:Face (Per c), su.chord (faceValue V u)/O; have hd :0≤d:=Push.AbsoluteSums.budget_nonneg hD.three; have hD':0 ≤ Λ :=Push.AbsoluteSums.budget_nonneg hD.two
   have ha : A ≤ l * ((N:ℝ)*e+4*d+Λ+Fintype.card PlaqAxes)-R:=by
          have hm:= YM.Massive.Pressure.exponent_retains hD (show (0:ℝ)<2*gaugeSize L x by positivity) ht.1 (ht.2 β hβ hB).1 V
          have hq := (abs_le.mp (Rain.second id 2 S.Z.page (S.Z.cost historyT.ht) historyT.ht V)).1
          have hn := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg N (α:=ℝ)); change R- l* _ ≤ _ at hm; change ↑N * -(l*e) ≤ _ at hn
          unfold A scent Reggae.pulse; have hu : l*PathData.loopsPrice p β d Λ ≤ l*(4*d+Λ):= mul_le_mul_of_nonneg_left ((ht.2 β hβ hB).2 d Λ hd hD') (Nat.cast_nonneg _)
          linarith only [hm,hn,hu]
   have hu : ‖X‖ ≤ l*Globe.bPeak M N:= Globe.engineR N (D' V) (hM v c S m (hm.trans h7) _ h10 h11 V)
   let B:=songT (c:=c) (N:=N) (fan L η x)⁻¹; obtain ⟨hc,hT⟩:=wordy b' F hF hp.ball V; have hR : ‖B‖ ≤ 1:=Globe.cache h8
   let K0 := heartK F.K p.threshold V
   have hl: 0 ≤ l:=Nat.cast_nonneg _
   have hL:‖K0‖ ≤ Real.exp l:=hc.trans (mul_le_of_le_one_left (Real.exp_pos _).le hR)
   have hy:‖Y‖ ≤ l:=hT.trans (le_trans (b:=‖B‖ * l) (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hl ((le_abs_self _).trans h9)) (norm_nonneg _)) (mul_le_of_le_one_left hl hR)) -- chip vs abs
   have hxy : ‖exp (X+Y)‖ ≤ Real.exp (l*(Globe.bPeak M N)+l):=by
          linarith [(norm_sub_norm_le (exp (X+Y)) (1:EvenA c N)).trans (stipend _ ((norm_add_le X Y).trans (add_le_add hu hy))), show ‖(1:EvenA c N)‖=1 from norm_one]
   change ‖exp (baker c N A+X+Y)*K0‖ ≤ Real.exp (l*(W+2)-R)
   rw [add_assoc,censor, smul_mul_assoc, norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
   refine (mul_le_mul (Real.exp_le_exp.mpr ha) ((norm_mul_le ..).trans (mul_le_mul hxy hL (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_
   rw [←Real.exp_add,← Real.exp_add]; apply congr_arg; unfold W; ring
end price
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.unmarked
