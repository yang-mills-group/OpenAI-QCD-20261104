import YM.Massive.Sharp.Core
/-! # Work towards trajectory pressure under Mark: L1 majorants -/
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open Grass


open Grass Patron
variable (A: Voice f N) (i₀:Flavor N) (T) (B: Badge P₀ τ R P o χ T U b (run S.L x) r β μ z)


local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Reference
-- one-step transfer along same stopping parameters. No growth frame of F along unchosen schemes.
variable {A3 tol:ℝ}{E:ℕ→SunR Ω}{Xb:ℕ→ℝ}{Ut:ℕ→Towers J.L}
variable (F₀:Flavor N)(M₀:Arrow N) (B:SparkMesh) {M':ℕ→ SparkMesh} (g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:PassageX τ D B M' F₀ χ g Ω E Xb Ut x κ s₀ 1 μ z 1 W' H A' (1/8) o A3 tol)
set_option quotPrecheck false
local notation "f₁"=> towerQ J B n i k
local notation "c₁"=> towerQ J B n (i+1) k
variable {t:ℝ}{Δ:PlaqAxes} {V1 U1 W1:ℕ→ℝ}{Pt:ℕ→BudgetPoint}{D0 a3 Q₀ ξ:ℝ}{Q1:∀ j,Pixel (towerQ J B n j k) N}
-- implicit tol not from above? A3 variables namespace shadow from Bank; outside ended.Bank need declare. see compile.
local notation "xg"=> delay J n i x
local notation "xo"=> delay J n (i+1) x
open Conductor Conductor.Quant High Meridians Ruby High.PrismT Massive.Filament
variable (hZ: Moor t T' B F₀ g Pt E (fun i=> g.costP i+N*Xb i) κ x τ.t D W' k V1 U1 W1 Q1 Δ s₀ tol)
variable (F:∀ j,ℂ→Pixel (towerQ J B n j k) N)
open Aperture Conductor.Quant
open Kin Sway OrbitG MeasureTheory NormedSpace
variable (G₀: Gem c N I)(T: Patron.Rail c N J')
open Finset
namespace Sharp
namespace Price
open Next.Rank IV Rain
section price
-- d,Λ invoice bound; nonpositive d/Λ implies absurd from path. could abs-max.
variable (P : Plan j) (T : Teller su) (L : Side) (Ω : ParcelR) (a d Λ κ η : ℝ)
variable (historyT : Ω.Rates σ)
include historyT
theorem protoK (hη : 0 < η) (hκ : 0 < κ) (Z Q:ℝ): ∃ K:ℝ,
    ∀ᶠ x in atTop, ∀ (c : Side) (p : BudgetPoint), Now L p T.top x → ∀ (F:Voice c N),
    Struck.Library.Cheap F.P F.K p L x η Z Q → ∀ (V : Grid c) (v : Train j) (S : SunR Ω) (D : PathData su),
    D.Bounds T.top.clip a d Λ → ∀ β m:ℝ, run L x/2 ≤ β → β ≤ 2*run L x → |m|≤roofK L η κ x →
    ‖NormedSpace.exp (heartS F.P p.threshold (scent S.Z.page p D T.top.clip β 0 N) (FieldB Ω S c (haloK L x) P v + m • 1) V)‖ ≤
      YM.Massive.Pressure.major su c K (2*gaugeSize L x/strength T.top.clip) V:=by
   obtain ⟨M,hM⟩:= Globe.uniformVeil P Ω historyT 1
   let e := 2^2 * (Smoke.expPrice 2 Ω.t*Ω.e)
   let W := Globe.bPeak M N + (↑N*e + 4*d + Λ + Fintype.card PlaqAxes)
   refine ⟨W+Z,?_⟩
   filter_upwards [Reference.prices T.top L η κ hκ hη] with x hx c p hp F hF V v S D hD β m hβ hB hm
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
   have hU : 1≤taxK L x 1:=Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le)
   let K0 := heartK F.K p.threshold V
   have hL:‖K0‖ ≤ Real.exp (l*Q):=mini (T:=F.K) V hF.bill hU (by norm_num) h8
   have hy:‖Y‖ ≤ l * Z:=Sharp.model F.P hF.shelf V (by norm_num) h8
   have hxy : ‖exp (X+Y)‖ ≤ Real.exp (l*(Globe.bPeak M N)+l*Z):=by
          linarith [(norm_sub_norm_le (exp (X+Y)) (1:EvenA c N)).trans (stipend _ ((norm_add_le X Y).trans (add_le_add hu hy))), show ‖(1:EvenA c N)‖=1 from norm_one]
   change ‖exp (baker c N A+X+Y)‖ ≤ Real.exp (l*(W+Z)-R)
   rw [add_assoc,censor, norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
   refine (mul_le_mul (Real.exp_le_exp.mpr ha) hxy (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_
   rw [← Real.exp_add]; apply congr_arg; unfold W; ring
end price
end Price
end Sharp
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Price.protoK
