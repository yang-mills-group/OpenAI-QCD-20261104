import YM.VStages.Votaries
import YM.VStages.Through
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
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
abbrev Station (p:BudgetPoint)(x:ℝ)(i:ℕ) := Now (seat P₀ A i) p (P.stage (A.level i)) (clockK P₀ A x i)
lemma waking (h:Station P₀ A R x i): Now (A.spacing i) R (P.stage (A.level i)) (clockQ P₀ A x i):= Spire.goNow (terminal P₀ A i x).symm h
lemma birthBook (h:Station P₀ A R x (i+1)): Now (A.spacing i) R (P.stage (A.level (i+1))) (run (A.spacing i) (clockQ P₀ A x i)):=by rw [Station,start_clock,notch] at h; exact h
lemma wages (p i):MassBox P₀ A p (i+1)= roofK (A.spacing i) θ (valueK P₀ A i) (run (A.spacing i) (clockQ P₀ A p i)):=by rw [MassBox,start_clock,notch,Nat.add_sub_cancel]
lemma wage_slot (_hi:i ≤ n)(a:ℝ): ArcTime A x i a→ run (seat P₀ A i) (clockK P₀ A x i)/2 ≤ a∧ a≤2* run (seat P₀ A i) (clockK P₀ A x i):=by rw [clockK,Spire.Client.fall]; exact id
namespace Affair
open Finset Grass NormedSpace MeasureTheory High PrismT
open Lunar Ring0 Stew.Project Sq
set_option quotPrecheck false
variable (B: SparkMesh) (T: Affair P₀ A X B x n)
local notation "q₀"=> clockQ P₀ A x i
local notation "Y₁"=> T.W.state (i+1)
local notation "Y₀"=> T.W.state i
local notation "ϕi"=> stepper P₀ A X B T i
local notation "Lₜ"=> A.spacing i
local notation "cₜ"=> A.ring (B.n k) i
local notation "cᵢ"=> A.ring (B.n k) (i+1)
local notation "Kq"=> K
abbrev Zest (p:ℕ→BudgetPoint)(i k:ℕ)(S:Voice (A.ring (B.n k) i) N)(β m:ℝ): Pixel (A.ring (B.n k) i) N :=
    let t:=T.W.state i; let s:= clockK P₀ A x i; quoteF _ S (J (A.level i)) t.wing (P.stage (A.level i)).clip t.path (p i) t.sun (haloK (seat P₀ A i) s) β m
abbrev SupportH (Pt:ℕ→BudgetPoint)(i k:ℕ)(Y:Pixel (A.ring (B.n k) i) N)(β m:ℝ):Prop :=
    let s:= clockK P₀ A x i; ∃ (S:Voice (A.ring (B.n k) i) N)(u:ℝ), 0 < u ∧ Enn (Pt i) F₀ (seat P₀ A i) s θ (1/8) (duo S.P S.K) ∧ Y=u • Zest P₀ A X B T Pt i k S β m
abbrev downF (i k:ℕ)(w β:ℝ)(Z:Pixel (A.ring (B.n k) (i+1)) N): Pixel (A.ring (B.n k) i) N:= vest _ _ w (fortQ (stepper P₀ A X B T i) Kq (Track.next A (B.n k) i) N β Z)
abbrev field (i k:ℕ):= FieldB (Fog.Mist.rate (A.town i).1) (T.W.state i ).sun (A.ring (B.n k) i) (haloK (seat P₀ A i) (clockK P₀ A x i)) (J (A.level i)) (T.W.state i).wing
abbrev event (Pt:ℕ→BudgetPoint)(Δ:PlaqAxes)(i k:ℕ)(W:Pixel (A.ring (B.n k) i) N) (d μ Ξ β m:ℝ):Prop := NormG (field P₀ A X B T i k) F₀ W (Pt i) (T.W.state i).path (P.stage (A.level i)).clip (T.W.state i ).sun.Z.page Δ d μ Ξ β m
variable (Pt:ℕ→BudgetPoint)

lemma from_eq (S:Voice (A.ring (B.n k) (i+1)) N)(α β:ℝ):
    Zest P₀ A X B T Pt (i+1) k S α β = quoteF cᵢ S (J (A.level (i+1))) (ϕi).wing (P.stage (A.level (i+1))).clip (Y₁).path (Pt (i+1)) (starting P₀ A X B T i) (haloK Lₜ (run Lₜ q₀)) α β :=by
    unfold Zest; rw [notch,start_clock]; rfl
lemma to_eq (h:i<n)(Y:Voice (A.ring (B.n k) i) N)(α β:ℝ):
    Zest P₀ A X B T Pt i k Y α β = quoteF cₜ Y (J (A.level i)) (ϕi).land (P.stage (A.level i)).clip (Y₀).path (Pt i) (closing P₀ A X B T i) (haloK Lₜ q₀) α β:=by
    rw [Spire.curtain (terminal P₀ A i x),show (ϕi).land=(Y₀).wing from (T.W.steps i h).landed]; rfl
lemma field_eq (h:i<n)(k:ℕ): FieldB ((A.beam i).fare) (closing P₀ A X B T i) (A.ring (B.n k) i) (haloK (ϕi).L q₀) (J (A.level i)) (ϕi).land= field P₀ A X B T i k:=by
    rw [show (ϕi).land=(Y₀).wing from (T.W.steps i h).landed, show (ϕi).L=Lₜ from rfl,Spire.curtain (terminal P₀ A i x)]; rfl
abbrev fare (i:ℕ):=2*|A.scale x (i+1)| + |T.W.delta A N i| +1
set_option quotPrecheck false
abbrev board (k i:ℕ)(Δ:PlaqAxes)(d μ Ξ:ℝ): Prop:= EveningR (A.ring (B.n k) i) (Pt i) (T.W.state i).path (P.stage (A.level i)).clip (A.spacing i) (clockQ P₀ A x i) (X i).policy.t (P₀ (A.node i)).V (fare P₀ A X B T i) F₀ Δ (roofK (A.spacing i) (X i).policy.t (valueK P₀ A i) (clockQ P₀ A x i)) d μ Ξ tol
lemma investment (h:ArcTime A x (i+1) α): |α+T.W.delta A N i|+1≤ fare P₀ A X B T i :=by
   have hp : |α| ≤2*|A.scale x (i+1)|:=by obtain ⟨h,h'⟩:= h; apply abs_le.mpr; constructor <;> linarith [abs_nonneg (A.scale x (i+1)),le_abs_self (A.scale x (i+1))];
   exact add_le_add_left ((abs_add_le ..).trans (add_le_add_left hp _)) 1
variable {Δ:PlaqAxes}
set_option maxHeartbeats 850000 in
lemma descends (hcX:Growth P₀ gate) (h₀:Station P₀ A (Pt i) x i)(hz:Station P₀ A (Pt (i+1)) x (i+1))(hβ:ArcTime A x (i+1) α)(hi:i<n) (hBox : |b|≤ MassBox P₀ A x (i+1)) (hp:0 < MassBox P₀ A x i)(Y:Pixel (A.ring (B.n k) (i+1)) N)(hT:SupportH P₀ A X B T Pt (i+1) k Y α b) (he:board P₀ A X B T Pt k i Δ d μ H) : ∃ w m z:ℝ, let F:=downF P₀ A X B T i k w α Y; let β:=α+T.W.delta A N i+z;
    0<w∧ w≤4∧|w-1|≤2*tol+tol^2∧ |z| ≤ 2 ∧ SupportH P₀ A X B T Pt i k F β m ∧ ForceMass b (MassBox P₀ A x (i+1)) m (MassBox P₀ A x i) ∧ (∀ U:Grid (A.ring (B.n k) i),advanceF (stepper P₀ A X B T i) Kq (Track.next A (B.n k) i) Y α U=gBody _ w (F U)) ∧ 1/4≤unitF true cₜ (field P₀ A X B T i k 1) ∧ event P₀ A X B T Pt Δ i k F d μ H β m :=by
    rw [wages P₀ A] at hBox
    obtain ⟨S,c',hS,hU,rfl⟩:= hT -- missing ξ!
    obtain ⟨U,hx,hh,hL,hY,Z,W₀,Hw⟩:= available (k:=k) P₀ A X B T hi (Pt (i+1)) (Pt i) (birthBook P₀ A hz) (waking P₀ A h₀) hβ hBox
    let f:= Zest P₀ A X B T Pt (i+1) k S α b
    let R0:=starting P₀ A X B T i; let R1:=closing P₀ A X B T i; let L1:=ϕi; let x':=q₀; let τ:= (X i).policy
    rw [notch,start_clock] at hU
    have hF:f= red S.P S.K R0 (J (A.level (i+1))) L1.wing (Pt (i+1)) U.up (city P (A.node i)).top.clip (haloK L1.L (run L1.L x')) α b 0:=by rw [hx]; exact from_eq ..
    have hE: EveningR cₜ (Pt i) U.down (P.stage (A.level i)).clip L1.L x' τ.t (P₀ (A.node i)).V (fare P₀ A X B T i) F₀ Δ (roofK L1.L τ.t (valueK P₀ A i) x') d μ H tol:=by rw [hh]; exact he
    have hb: MassBox P₀ A x i ≤ ((L1.L.val:ℝ)/128-1)*roofK L1.L τ.t (valueK P₀ A i) x':=by unfold τ; rw [(X i).theta]; exact ceilingW P₀ A hcX hp.le
    obtain ⟨Y,w,m,c0,z,hw,hw4,hc,hR,hq,h2,hC,hE',hW,ht,hN⟩:= Cairn.sojourn (χ:=χ) (J (A.level (i+1))) (J (A.level i)) F₀ S W₀ Z Hw hS hL hY (show Enn (Pt (i+1)) F₀ L1.L (run (A.spacing i) (clockQ P₀ A x i)) (X i).policy.t (1/8) (duo S.P S.K) from by rw [(X i).theta]; exact hU) (investment P₀ A X B T hβ) hE _ hb -- alt binder
    rw [← hF] at hW hE' hN; change 1/4 ≤ _ at ht; rw [field_eq P₀ A X B T hi k] at ht hN
    refine ⟨w,m,z,hw,hw4,hc,hR,?_,?_ ,hW,ht,?_⟩
    · refine ⟨Y,c0,hC,?_,?_⟩
      · rw [(X i).theta] at h2; exact Spire.germSet (terminal P₀ A i x) F₀ Y h2
      rw [to_eq P₀ A X B T Pt hi]; rw [hh] at hE'; exact hE'
    · rw [wages P₀ A]; simp_rw [(X i).theta] at hq; exact hq
    rw [hh] at hN; exact hN
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.descends
