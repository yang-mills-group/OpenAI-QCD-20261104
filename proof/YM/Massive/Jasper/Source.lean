import YM.Massive.Jasper.Corpus
/-!
# Verified massive trajectory candidates with unequal reference-scale RG SIGNALS

Work towards Theorem 1 (unequal-flavor positive-renormalized-mass) not itself that result. Noncollapse masses here are in the displayed scheme of reading from the actual *effective density*; they are not determined from PCAC at reference length. Lavish schedule.Still allows arbitrary refined matching budget before asking even for a finite nonzero base β at one exact reference scale. Gauge history a calibrated slope **band at a fixed tolerance** plus actual window calibration to stiffness derivative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Sequence
open Filter Lattice Function QCD QCD.Lat
open scoped Topology
variable (C : Sequence)

-- all but the exact slope. β-slope can be given an arbitrarily tight band in the repeated theorem version.
structure PathBand (βRef ε η : ℝ) : Prop where
  choices : C.S.choices.penalty = 1
  initialStage : 4 ≤ C.S.J 0
  infinite : Tendsto (fun i => (C.R i).val) atTop atTop
  uv : StrictMono C.N
  physical : Tendsto (fun i => C.S.spacing (C.N i)) atTop (𝓝[>] 0)
  even (i) : Even (C.R i).val
  atLeast (i) : 4 ≤ (C.R i).val
  normalized (i) : (C.A i).Actual
  separate (i) : Injective (C.A i).u
  reference (i) : (C.A i).β 0 = βRef
  compare {i m} (h : m ≤ C.N i) : Stiffness.Window ((C.A i).density m) ((C.A i).β m) ε
  beta_min {i m} (h : m ≤ C.N i) : 1 ≤ (C.A i).β m
  size (m) : ∃ B : ℝ, ∀ i, m ≤ C.N i → (C.A i).β m ≤ B
  near {i m} (h : m < C.N i) : |(C.A i).w m - 1| ≤ ε
  runs : 0 < betaSlope ∧ ∀ᶠ m : ℕ in atTop, ∀ i:ℕ,m ≤ C.N i → |(C.A i).β m/Real.log ((C.S.spacing m)⁻¹)-betaSlope| ≤ η

-- The additional physical laws calibrated at the reference from the signals of physics are NOT part of the price claim
structure Service (v:Flavor 6→ℝ)(d:ℝ) : Prop where
    margin : 0<d
    pos i : d ≤ v i
    leave i j (h:i ≠ j) : d ≤ |v i-v j|
    tendency (i : Flavor 6): Tendsto (fun j=>(C.A j).massRead 0 i) atTop (𝓝 (v i:ℂ))

lemma better {β ε η:ℝ} (h:C.PathBand β ε η)(he:C.Slope): C.Path β ε:=
    ⟨h.choices,h.initialStage,h.infinite,h.uv,h.physical,h.even,h.atLeast,h.normalized,h.separate,h.reference,h.compare,h.beta_min,h.size,h.near,he⟩

end YM.Massive.Sequence
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
open Next.Rank IV Rain
namespace Jasper
open Glint
open High.PrismT Globe Massive.Reading
variable (L1:HaarBudget su)(F':ℂ→Pixel c N)(D':PathData su)
variable {hj:J.Branches T'.bind su}{K1 b₁ b₂ p:ℝ}
variable (Y:∀ j,LanternT (towerQ J B n 0 k) N (towerQ J B n j k)) (hP:Regular L1 (1/2) K1 b₂ T' Q B F₀ x κ τ g Pt E (fun i=> g.costP i+N*Xb i) D W' k V1 U1 W1 Q1) -- common θ fix
variable (hk: CarrierL J.L T'.top N ε D0 A3 a3 Q₀)(hC:Sharp.Purer T' J Ω N x τ.t a d Λ κ ε D0 b₁)(hp: Gallery T' J n k B N V1 W1 Q1 Y hj)
variable (hw: Fueled T' B F₀ M₀ V1 U1 g Pt E τ.t x ε D0 k Y p v)(ht:Sharp.Attendance F₀ M₀ B Y τ.t D0 ε b₁ b₂ w v E Pt T' V1 U1 L1 x g)
open Sharp
local notation "sY"=>ShapeX B Y M₀.tip v
local notation "qX"=> gainsW B Y M₀ τ.t x
local notation "φ"=>Rotary.chartR
open Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open scoped ComplexOrder
variable (heJ:J.Branches T'.bind su) {V':ℕ→Bed} {A0 φ₀:ℝ}
-- specialize separation from `fork` (not pattern in following six) predicate useful.Price.A.Band
variable (R6:Grant L1 χ J (0:Flavor 6) fork Q a d D A3 a3 A0 tol ε D0 Q₀ heJ ν)
variable (hC6:Cab (0:Flavor 6) fork L1 heJ R6 x B)(he6: KeyL J ε D0 R6.κ σ)
local notation "tM!"=> measureR J x R6.policy.t ε σ
local notation "qS!"=> positiveAnswer J x R6.κ R6.policy.t
open Next.Rank Massive.Sequence
variable (Y6: Corpus B J T' heJ)
include hC6
-- PathBand matches Statement.Tower exactly except slope. Encode limit.Separate check not |
lemma tracking (h: Screen L1 heJ B R6 Y6 x η σ)(ht:tol+tol+tol^2≤ν)(hJ:J.J=4)(h1:T'.bind.penalty=1) : PathBand (Corpus.sequence B heJ Y6) (run J.L x) ν η ∧ Service (Corpus.sequence B heJ Y6) Y6.limit (Glint.Value (tM!)):=by
   let m:=Y6.mark; let X(i):= Y6.A i; let A:= Corpus.sequence B heJ Y6; let M:=Glint.Value (measureR J x R6.policy.t ε σ); have hX(i:ℕ):= grants (0:Flavor 6) fork B L1 heJ R6 _ _ (h.boot i)
   change PathBand A (run J.L x) ν η ∧ Service A _ M; refine ⟨?_,⟨(by unfold M Glint.Value; have hx:=h.measure; positivity),fun i=>(h.separate.margin i).1,h.separate.apart,h.massPart⟩⟩
   refine ⟨h1,hJ.ge,h.period,h.lift,h.small,?_,fun i=>hC6.tlim _,fun i=>(hX i).2.2.1,fun i=>(hX i).2.2.2.1,fun i=>(hX i).1,fun {i j} hi=> (hX i).2.2.2.2.2.1 j hi, fun {i j} hi=> ((hX i).2.1 j hi).1,fun m=>⟨2*run J.L (tallyK J.L x m),fun i hi=> ((hX i).2.1 m hi).2.1⟩,fun {i m} hi=> ((hX i).2.2.2.2.1 m hi).trans ht, SIX.2, h.slopePart⟩
   intro i; change Even (B.n _).val; rw [hC6.next,PNat.mul_coe]; exact hC6.unit.mul_right _
omit hC6
-- assemble Clock. tolerance after Est choice.W near one ensures any ε. Enorm Ende.Comp.
lemma insured (ε:ℝ)(he:0<ε):∃ t:ℝ,0<t∧t+t+t^2≤1/2∧t+t+t^2≤ε:=by
    let t:=min (ε/3) (1/8); refine ⟨t,lt_min (by positivity) (by norm_num), ?_⟩; have ht:t≤ 1/8:= min_le_right ..; have he':0<t:=lt_min (by positivity) (by norm_num); have hp:t ≤ ε/3:=min_le_left ..; constructor<;> nlinarith only [ht,hp,mul_le_mul_of_nonneg_right ht he'.le]

section six
variable (G6:CarrierL J.L T'.top 6 ε D0 A3 a3 Q₀)(h6:Estate L1 χ J (0:Flavor 6) fork Q a d D A3 a3 A0 tol ε D0 Q₀ heJ)
abbrev salary (L':Patch)(τ:ℝ)(β ε σ:ℝ) := Glint.Value (measureR L' (clockX L'.L β) τ ε σ) -- T' unused remove
-- dialectic embedding. explicitly ∀ᶠ β support after φ choice but q=measureR(χ)>0 any Key φ. preserve all.
structure FullCall (L1:HaarBudget su)(Q:ConnectedActivityE6.Target su T')(χ:Chi)(J:Patch)(a d D A3 a3 A0 K:ℝ)(tol ε D0 η ν:ℝ)(he:J.Branches T'.bind su) :Prop where
     story : ∃ R:Grant L1 χ J (0:Flavor 6) fork Q a d D A3 a3 A0 tol ε D0 K he ν, Priority (0:Flavor 6) fork L1 he R ∧ (∃ σ:ℝ,KeyL J ε D0 R.κ σ)∧ ∀ᶠ β in atTop, ∃ B:SparkMesh, Cab (0:Flavor 6) fork L1 he R (clockX J.L β) B∧∀ σ:ℝ, KeyL J ε D0 R.κ σ→∃ Y:Corpus B J T' he, Screen L1 he B R Y (clockX J.L β) η σ∧ PathBand (Corpus.sequence B he Y) β ν η ∧ Service (Corpus.sequence B he Y) Y.limit (salary J R.policy.t β ε σ)
include heJ G6 h6
lemma opensV (hr:0<η)(hν:0<ν)(hD:D+2≤η/2* Real.log J.L.val)(hK:T'.bind.penalty=1)(hJ:J.J=4)(hL:1<J.L.val)(ht:tol+tol+tol^2 ≤ ν): FullCall L1 Q χ J a d D A3 a3 A0 Q₀ tol ε D0 η ν heJ:=by
   obtain ⟨R,Hp,H⟩:= grant (0:Flavor 6) fork L1 G6 heJ hL hν hJ.ge splitU h6 -- Notice `hJ.ge`: RHS maybe direction ok
   refine ⟨⟨R,Hp, Glint.door G6.gives.fuel G6.gives.wedge Hp.κ_ok,?_⟩⟩; have hp : Tendsto (clockX J.L) atTop atTop := by unfold clockX; simp_rw [sub_eq_add_neg]; exact tendsto_atTop_add_const_right _ _ tendsto_id
   filter_upwards [hp.eventually H] with β hM; obtain ⟨B,hB⟩:=hM; refine ⟨B,hB,fun σ h=>?_⟩; obtain ⟨Y,hX⟩:= crystal B L1 heJ R hB h G6.gives.fuel hr hL hD; refine ⟨Y,hX,?_⟩; obtain ⟨hc,he⟩:= tracking B L1 heJ R hB Y hX ht hJ hK; rw [halt] at hc; exact ⟨hc,he⟩
omit heJ G6 h6
set_option maxHeartbeats 600000 in
/-- Main calibrated (full SU3 regulator / normalized trajectory) proof so far. -/
theorem stories {η ν :ℝ} (he:0<η)(hv:0<ν): ∃ (T': Teller su)(Q:ConnectedActivityE6.Target su T')(L':HaarBudget su)(s t D A3 a3 a4 ε D0 Q₀ tol:ℝ)(J:Patch), T'.bind.penalty=1 ∧ T'.top.supportExponent=2 ∧ T'.top.clip.direct ≤1∧ s=T'.top.width ∧t ≤T'.top.paths∧0 ≤ D∧0≤ A3∧0<a3∧J.J=4 ∧ 512≤J.L.val ∧2*(D+3) ≤ subG 6*Real.log J.L.val∧Massive.betaSlope=betaQ 6 ∧0 < betaQ 6∧ D+2 ≤ η/2 * Real.log J.L.val ∧0 < tol∧ tol+tol+tol^2≤1/2 ∧ tol+tol+tol^2≤ν∧∃ h:J.Branches T'.bind su, CarrierL J.L T'.top 6 ε D0 A3 a3 Q₀∧ Estate L' Chi.canonical J (0:Flavor 6) fork Q s t D A3 a3 a4 tol ε D0 Q₀ h ∧ FullCall L' Q Chi.canonical J s t D A3 a3 a4 Q₀ tol ε D0 η ν h:=by
    obtain ⟨T,Q,L',s,t,D,A3,a3,a4,ε,D0,Q₀,J,hK,hδ,hV,h0,h1,h2,hA,hC,H,hH,hG,hS,hX,hp,hj,ht,hx⟩:= rendition η he; obtain ⟨tol,hT,hZ,hP⟩:= insured ν hv; have h:= hx tol hT hZ; exact ⟨T,Q,L',s,t,D,A3,a3,a4,ε,D0,Q₀,tol,J,hK,hδ,hV,h0,h1,h2,hA,hC,H,hH,hG,hS,hX,hp,hT,hZ,hP,hj,ht,h, opensV L' hj ht h he hv hp hK H (by omega) hP⟩
end six
end Jasper
end Reference
end Rails
end YM.QCD.Acre
namespace YM.Massive.Sequence
open Filter QCD.Acre.Rails.Reference.Jasper QCD QCD.Lat
-- simple map to Sequences. βRef may be >0 etc automatic from cofinal horizon.
theorem travel {η ε:ℝ}(he:0<η)(hv:0<ε) : ∀ᶠ β in atTop,∃ (C:Sequence)(d:ℝ) (v:Flavor 6→ℝ), 0<β∧PathBand C β ε η ∧ Service C v d:=by
    obtain ⟨T,Q,L',s,t,D,A3,a3,a4,eps,D0,Q₀,tol,J,hK,hδ,hV,h0,h1,h2,hA,hC,H,hH,hG,hS,hX,hp,hT,hZ,hP,hj,ht,h,hx⟩:= stories he hv; obtain ⟨R,Hp,⟨σ,hQ⟩,hv⟩:= hx.story
    filter_upwards [hv,eventually_gt_atTop (0:ℝ)] with x hR hε; obtain ⟨B,hB,hR⟩:=hR; obtain ⟨Y,hB,hR,hC⟩:= hR σ hQ; exact ⟨Corpus.sequence B hj Y,_,_,hε,hR,hC⟩
end YM.Massive.Sequence
#print axioms YM.Massive.Sequence.travel
