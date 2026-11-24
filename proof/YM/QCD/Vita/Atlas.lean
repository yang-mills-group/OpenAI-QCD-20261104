import YM.QCD.Vita.Mesh
import Mathlib.Topology.MetricSpace.Equicontinuity
import YM.Extraction.Tame
import Mathlib.Topology.UniformSpace.Ascoli
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
open Push.BetaTransport Rain MeasureTheory
variable {M Rᵥ V U Wᵥ A₁ Y:ℕ→ℝ}
variable {j:ℕ} (B:SparkMesh)(O:Patch)
section limit
variable {S:ℕ→ℕ}(V U W:ℕ→ℕ→ℝ)(P: ℕ→∀ i,Pixel (finC O B i k) N)
variable (hp:∀ n:ℕ, Candor O B K M Rᵥ N n k x κ r (V n) (U n) (W n) (P n)) (ht:∀ i, 0<Rᵥ i)(hK:O.Branches K su) (hm:∀ y,x≤y→ Shade O.L r y)
variable {q':ℕ→ℕ} {V₀ U₀ W₀:ℕ→ℝ}{Y₀:∀ i,Pixel (finC O B i k) N}(hx: Hook B O V U W P q' V₀ U₀ W₀ Y₀)(he:Tendsto q' atTop atTop)
include hx he
lemma tall (j:ℕ): Tendsto (fun i:ℕ=> V (q' i) j) atTop (𝓝 (V₀ j))∧ Tendsto (fun i:ℕ=> U (q' i) j) atTop (𝓝 (U₀ j))∧Tendsto (fun i:ℕ=> W (q' i) j) atTop (𝓝 (W₀ j)):=⟨continuous_fst.continuousAt.tendsto.comp (hx.hm j),(continuous_fst.comp continuous_snd).continuousAt.tendsto.comp (hx.hm j), (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp (hx.hm j)⟩
include ht hp hK hm
lemma noons (j:ℕ):Candor O B K M Rᵥ N j k x κ r V₀ U₀ W₀ Y₀:= by
    have hh(i):∀ᶠ n in atTop,Continuous (P (q' n) i)∧Rain.realP (P (q' n) i) ∧ Cvol (P (q' n) i)=1 ∧ (∀ x, ‖P (q' n) i x‖ ≤ M i) ∧ GaugeM O i x/2 ≤ V (q' n) i ∧ V (q' n) i ≤ 2*GaugeM O i x ∧ |U (q' n) i|≤rangeG O i 0 κ r x:= (he.eventually_ge_atTop i).mono fun n h=> (hp (q' n)).capital i h
    have hF(i):=allowY B O V U W P hx i; have hG(i):= tall _ _ V U W P hx he i -- maybe extra includes
    refine ⟨?_,?_,?_⟩
    · intro i hi; let A(n:ℕ):= P (q' n) i; have hL:= hh i; have hM:∀ᶠ j in atTop, Continuous (A j)∧∀ V, ‖A j V‖≤M i:= hL.mono fun i h=>⟨h.1,h.2.2.2.1⟩
      refine ⟨(hF i).1,?_,tendsto_nhds_unique_of_eventuallyEq (priceV A (Y₀ i) (hF i).2 hM) tendsto_const_nhds (hL.mono fun _ h=>h.2.2.1),fun x=> le_of_tendsto ((hF i).2 x).norm (hM.mono fun k h=>h.2 _), ge_of_tendsto (hG i).1 (hL.mono fun k h=> h.2.2.2.2.1), le_of_tendsto (hG i).1 (hL.mono fun _ h=> h.2.2.2.2.2.1), le_of_tendsto (hG i).2.1.abs (hL.mono fun _ h=> h.2.2.2.2.2.2)⟩
      intro i'; have ht:Tendsto (fun j=>cBer (A j) i') atTop (𝓝 (cBer (Y₀ i) i')):= ((peakW (finC O B i k) N).continuous.tendsto _).comp ((hF i).2 i'); have hx:= Complex.continuous_re.continuousAt.tendsto.comp ht
      exact ⟨tendsto_nhds_unique_of_eventuallyEq ht (Complex.continuous_ofReal.continuousAt.tendsto.comp hx) (hL.mono fun k h=> (h.2.1 i').1), ge_of_tendsto (show Tendsto (fun j=> (cBer (A j) i').re) atTop (𝓝 _) from hx) (hL.mono fun k h=> (h.2.1 i').2)⟩
    · refine ⟨tendsto_nhds_unique_of_eventuallyEq (hG 0).2.1 tendsto_const_nhds (Eventually.of_forall fun i=> (hp _).mint.1),tendsto_nhds_unique_of_eventuallyEq (hG 0).1 tendsto_const_nhds (Eventually.of_forall fun i=> (hp _).mint.2)⟩
    intro i hi
    let a(n:ℕ):= q' n; let S:=Pike O 0; let Y:= powerV B O i k
    have hX:∀ᶠ n in atTop, i< a n:= he.eventually (eventually_gt_atTop i)
    have hz:= hX.mono fun n h=> (hp (a n)).vocals i h
    have hσ : Rᵥ i ≤ W₀ i:= ge_of_tendsto (hG i).2.2 (hz.mono fun _ h=> h.2.1)
    refine ⟨le_of_tendsto (hG i).2.2 (hz.mono fun i h=>h.1), hσ,fun u=>?_⟩
    let R:=GaugeM O (i+1) x; have hu:Tendsto (fun n=> advance S K Y (P (a n) (i+1)) (V (a n) (i+1)) u) atTop (𝓝 (advance S K Y (Y₀ (i+1)) (V₀ (i+1)) u)):=by
          refine tended (u:=M (i+1)) (w:=2*R) (S:=S) (h:=Y) (fun n=>P (a n) (i+1)) _ (hF (i+1)).2 (hG (i+1)).1 ((hh (i+1)).mono (fun n h=>?_)) hK u -- edit binder
          have ht := h.2.2.2.2; have hu:R>0:=(hm _ (matters ..)).value; exact ⟨(abs_of_nonneg (show 0 ≤ V _ _ from (lt_of_lt_of_le (half_pos hu) ht.1).le)).trans_le ht.2.1,h.1,h.2.2.2.1⟩
    exact tendsto_nhds_unique_of_eventuallyEq hu (rightV (fun n=> P (a n) i) (Y₀ i) (V:=fun n=>W (a n) i) (hG i).2.2 (hF i).2 ((ht i).trans_le hσ) u) (hz.mono fun n h=> h.2.2 _)
end limit
end Rails
end YM.QCD.Acre
