import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Shoot
import YM.Massive.Pressure.Minor
import YM.Massive.Pressure.Smoothed
import YM.Massive.Tuner.Flat
import YM.Massive.Tuner.Empty
import YM.Massive.Stiffness.Limit
import YM.Massive.Tuner.Common
import YM.Massive.Reference.Scaling
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



-- package six-flavor dataset explicitly (not `benz` mass confused with β)
variable {θc : ℝ} (Ω : ParcelR) (T:Teller su) (L1:HaarBudget su)

structure Favorite (S : Scheme) (F:ℕ) where
  R : ℕ → Side
  run (i:ℕ) : Massive.Run S (i+1) (R i) F
  signal : ℕ → ℕ → ℝ

structure Goalpost (L:Side) (S : Scheme) (F:ℕ) (rec : Favorite S F) (u β η:ℝ) (s:ℕ→ℝ) :Prop where
  period : Tendsto (fun i=> (rec.R i).val) atTop atTop
  even (i:ℕ) : Even (rec.R i).val
  atLeast (i:ℕ) : 4≤(rec.R i).val
  length (m:ℕ) : S.spacing m = ((L.val : ℝ)^m)⁻¹
  UV : Tendsto S.spacing atTop (𝓝[>] 0)
  -- Actual geometry & prices still at **positive-common** terminal shot.
  flow (i:ℕ) : (rec.run i).Actual
  common (i:ℕ) : ∀ a,(rec.run i).u a = rec.signal i (i+1)
  window (i m:ℕ) (h:m≤ i+1) : Massive.Stiffness.Window ((rec.run i).density m) ((rec.run i).β m) (s i)
  signalPos (i:ℕ) : rec.signal i 0=u
  real_mass : 0<u
  threshold : 0 < β
  budget (i m:ℕ) (h:m≤ i+1) : |rec.signal i m|≤1
  toward (i m:ℕ) (h:m≤ i) (b:Flavor F) : ‖(rec.run i).massRead m b - (rec.signal i m:ℂ)‖ ≤ s i
  βbase (i:ℕ) : (rec.run i).β 0=β
  βalive (i m:ℕ)(h:m≤ i+1):1 ≤ (rec.run i).β m
  tollB (m:ℕ):∃ v:ℝ, ∀ i:ℕ,m ≤ i+1 → (rec.run i).β m ≤ v
  slope : ∀ᶠ m in atTop, ∀ i:ℕ, m≤ i+1 → |(rec.run i).β m/Real.log ((S.spacing m)⁻¹)-betaQ F|≤ η
  start : S.choices.penalty=1

-- with exact history data related, witnessing prices afterwards.
variable (L1':HaarBudget su) (hw:O.Branches T'.bind su)

structure Track (T': Teller su)(Q:ConnectedActivityE6.Target su T')(J:Patch) (hw:J.Branches T'.bind su)(b:Flavor N) (V:ℕ→Bed)(T:ℕ→Towers J.L)(σ γ δ a d D s x:ℝ)(B:SparkMesh) (Ω:ParcelR) (τ: Policy Q T'.top N) (A K κ q:ℝ) (rec:Favorite (fixed J T'.bind hw) N) : Prop where
  align (i:ℕ) : ∃ (S:ℕ→SparkMesh)(g:PulseRide T'.bind T'.top.clip J a d S (i+1)) (X:ℕ→SunR Ω) (P:ℕ→BudgetPoint)(Y:ℕ→ℝ), Invoice g Q.table V T σ γ δ D s ∧
      ∃ (k:ℕ) (h:B.n k = rec.R i), ∃ U F W A', Regular L1 (1/2) A K T' Q B b x κ τ g P X Y D q k U F W A' ∧
        switch (i+1) F= rec.signal i ∧ rec.run i=h ▸ fly B hw U F W (i+1) k N

-- build Favorite choosing k per depth
variable {H : ℕ → Bed}
variable (Q : ConnectedActivityE6.Target su T') (τ: Policy Q T'.top N)

noncomputable abbrev positiveAnswer (O:Patch)(x κ τ:ℝ):= roofK O.L τ κ x*(1/2:ℝ)
lemma crossW {c f:Side} (h : c=f) {X:Density c N} (ht:Massive.Stiffness.Window X β ε) : Massive.Stiffness.Window (transit h X) β ε:=by subst f; exact ht
lemma crossP {c f:Side} (h : c=f) (X:Density c N)(b':Flavor N) : planeProbe (transit h X) b'=planeProbe X b':=by subst f; rfl

lemma favorite (hc: 3 ≤ O.L.val) (h1: T'.bind.penalty=1)
    {K₀ K₁:ℝ}
    (L1':HaarBudget su)
    (hr: ReadyR Ω (passportM O.J O.order_cut) O T'.bind T'.top.clip a d T'.η T'.C T'.C)
    (hs:Even (B.n 0).val)(he:∀ i, B.n i=B.n 0*O.L^i)(hx:∀ i,4≤(B.n i).val)
    (hE:∀ n:ℕ,0<n→ ∃ (S:ℕ→SparkMesh)(g:PulseRide T'.bind T'.top.clip O a d S n) (X:ℕ→SunR Ω), ∃ P Y, Invoice g Q.table H T₁ σ γ δ D s ∧∀ k:ℕ,∃ U F W A', Regular L1' (1/2) K₀ K₁ T' Q B b' x κ τ g P X Y D W' k U F W A')
    (hM:∀ ε:ℝ,0<ε → ∀ᶠ c:Side in atTop, Signal Ω O.L (passportM O.J O.order_cut) ε κ τ.t x b' c)
    (prec:ℕ→ℝ)(hP:∀ i,0 < prec i)(hq:0 < η)(hA:D+2 ≤ η/2 * Real.log O.L.val) : ∃ rec : Favorite (fixed O T'.bind hw) N, Goalpost O.L (fixed O T'.bind hw) N rec (positiveAnswer O x κ τ.t) (run O.L x) η prec ∧ Track L1' T' Q O hw b' H T₁ σ γ δ a d D s x B Ω τ K₀ K₁ κ W' rec:=by
    -- choose price dataset, period, then shoot in it
    have hh (i:ℕ):= hE (i+1) (by omega); choose S F X P Y hI H using hh
    choose V U W A hK using H
    have hz (i:ℕ): ∀ᶠ k in atTop, FitLevel L1' τ B b' (F i) K₀ K₁ (P i) (X i) (Y i) κ x D W' (prec i) k:= accurate _ _ _ _ hr.1 (hM _ (hP i)) (hK i 0).clock (hI i) (hP i)
    choose k w hk using fun i=> ((hz i).and (eventually_ge_atTop i)).exists
    let A0 (i:ℕ):= fly B hw (V i (k i)) (U i (k i)) (W i (k i)) (i+1) (k i) N
    let c := B.n ∘ k; let T (i : ℕ):=switch (i+1) (U i (k i)); let μ:= positiveAnswer O x κ τ.t
    let R : Favorite (fixed O T'.bind hw) N:=⟨c,A0,T⟩; have hi (i:ℕ) := hK i (k i)
    have hfit (i m:ℕ) (hm : m≤ i+1):= (w i).attend _ _ _ _ _ (hi i) m hm -- inferred implicit?
    have hz (i:ℕ): Even (c i).val:= by unfold c; rw [Function.comp_apply,he,PNat.mul_coe]; exact hs.mul_right _
    have life(i:ℕ) : rangeG O (i+1) (i+1) κ τ.t x=roofK O.L τ.t κ x := by simp [rangeG,delay,tallyK]
    refine ⟨R,⟨?_, hz,fun i=> hx _, fun m=> ratioSpacing hw _,lifetime O hw (by omega), fun i=> escrow _ _ (F i) _ hw (hi i) (hz i) (hx _),?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h1 ⟩, ⟨fun i => ?_⟩⟩ -- Track constructor
    · exact B.cofinal.comp (tendsto_atTop_mono (fun i=> hk i) tendsto_id)
    · intro i a; change U i _ _=switch _ _ _; simp [switch]
    · intro i j hj; let W:=i+1-j; have hh: W+j=i+1:= Nat.sub_add_cancel hj; have hW : W≤ i+1:= Nat.sub_le ..
      let hD:= expand B hw _ _ hh (k:=k i); obtain H:=charter _ _ _ _ hw (hi i) W hW j hh hD; change Massive.Stiffness.Window ((fly B hw _ _ _ _ _ _).density _) (V i (k i) W) _; rw [H]; exact crossW hD (hfit i W hW).1 -- helper
    · intro i; obtain he := (hi i).finish.2; change switch _ _ _=_; rw [switch,Nat.sub_zero]; rwa [life] at he
    · have ht:0< roofK O.L τ.t κ x:= (life 0) ▸ ((hi 0).costs 1 le_rfl).2.1; unfold positiveAnswer; positivity
    · rw [← (hi 0).finish.1]; exact zero_lt_one.trans_le ((hi 0).beta _ le_rfl)
    · intro i m hm; exact (hi i).mass _ (Nat.sub_le (i+1) m)
    · intro i m hm b; let W:=i+1-m; have hh: W+m=i+1:=Nat.sub_add_cancel (by omega); have hW:W≤ i+1:=Nat.sub_le ..; have hw': 0 < W:=by omega
      let hD:= expand B hw _ _ hh (k:=k i); obtain H:= charter _ _ _ _ hw (hi i) W hW m hh hD; change ‖planeProbe ((fly B hw _ _ _ _ _ _).density _) b-(U i (k i) W:ℂ)‖≤_; rw [H,crossP]; exact (hfit i W hW).2 hw' b
    · intro i; change V i (k i) _= _; exact (hi i).finish.1
    · intro i m hm; exact (hi i).beta _ (Nat.sub_le (i+1) m)
    · intro m; refine ⟨2*run O.L (tallyK O.L x m),fun i hi'=>?_⟩; let j:= i+1-m; have hj:j≤ i+1:=Nat.sub_le ..; refine ((hi i).costs j hj).1.2.trans_eq ?_; unfold hatG delay; rw [show i+1-j=m from (by omega)]
    · filter_upwards [Reference.within (N:=N) O hw (by omega) hq hA (W':=W') (x:=x)] with m hm i hi'; exact hm _ (Reference.toll _ _ _ _ (hi i) hw m hi') -- args
    exact ⟨S i,F i,X i,P i,Y i,hI i,k i,rfl,_,_,_,_,hi i,rfl,rfl⟩
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.favorite
