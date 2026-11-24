import YM.QCD.Reef.Grant
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
namespace IV
variable {u':ℝ} (T:ParcelR) (A:Plan 4)
open MeasureTheory
lemma whole (L:Side)(k:ℕ)(hp:3 ≤ L.val) (M:ℕ):∃ (B:Side), M ≤ B.val∧∀ᶠ x in atTop,∃ j:ℕ,sFirst L k (run L x)=B*L^j:=by
     have hr:M ≤ L.val^M:=(Nat.lt_pow_self (one_lt_two.trans_le (by omega))).le; refine ⟨boostF (stellar (L^M) 4),by unfold boostF stellar; simp only [PNat.mul_coe,PNat.pow_coe]; change M ≤ 2*(L.val^M*(3:ℕ)^4)*3; omega,?_⟩
     apply (Work.E09.betaF_growth su L).eventually (p:=fun (y:ℝ)=> ∃ j:ℕ,sFirst L k y=boostF (stellar (L^M) 4)*L^j)
     filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (L.val^M)] with x hx; -- let j
     let t:=visual L k x; have he:M ≤ t:=by
          have hv : L.val^M ≤ Hearth.vizR x:=by unfold Hearth.vizR; nlinarith
          apply le_trans (b:= Nat.log L.val (Hearth.vizR x));
          · exact Nat.le_log_of_pow_le (by omega) hv
          unfold t visual; exact le_trans (Nat.le_add_right _ 1) (Nat.le_max_right ..)
     refine ⟨t-M,?_⟩; change boostF (stellar (L^t) 4)=_; have ht:L^t=L^M*L^(t-M):=by rw [← pow_add,Nat.add_sub_cancel' he]
     rw [ht]; unfold boostF stellar; ac_rfl
structure Sipping (L c: Side)(h:ℝ)(X:ParcelR)(P:Plan j)(F:Flavor N)(x T:ℝ)(B:Clip)(b σ s:ℝ):Prop where
    costs:∀ (i:ℕ)(n:Side)(p:PathData su)(E:BudgetPoint)(u:SunR X)(Z: Pixel n N)(Y:Voice n N)(K:Train j)(κ:ℝ), n=c*L^i→ Enn E F L x h (1/8) (duo Y.P Y.K) → p.Bounds B b σ s→0 < κ→ realP Z→ Z=κ • red Y.P Y.K u P K E p B (haloK L x) (run L x) 0 0 → κ*Globe.expo T n ≤ (cBer Z 1).re
lemma nectar (hr:T.Rates η)(X:Clip)(σ s b:ℝ)(M:Side)(hv:0<u')(hp: Globe.DomainF A N L M W): ∀ᶠ x in atTop,∃ Z:ℝ,Sipping L M u' T A b' x Z X σ s b:=by
    obtain ⟨v,w,hv',hw,hP⟩:=hp.port
    filter_upwards [honey (L:=L) b' (zero_lt_one.trans_le hw) hv' hv] with x hx; obtain ⟨K,hK,H⟩:=sens _ hr X σ b s |run L x| N
    refine ⟨K+W, ⟨fun i c p E u Z Y U κ hc hE hz ht hV hZ=>?_⟩⟩; rw [flatR A Y Z _ _ _ _ U hV hZ ht]; obtain ⟨hm,hp⟩:=hx E c Y hE 1
    let T':= Patron.total Y.P E.threshold (1:Grid c); have hT: Globe.expo W c ≤ Globe.pebble (paleF N (Globe.sunny A U c)+T'):=by
         obtain ⟨f,g,h,-⟩:=hE; exact hP i c hc U _ (appetite Y.P Y.K h.pan hm) hp
    unfold Globe.expo; rw [mul_add,Real.exp_add, ← mul_assoc]; apply mul_le_mul _ hT (Real.exp_pos _).le (mul_pos ht (Real.exp_pos _)).le; apply mul_le_mul_of_nonneg_left _ ht.le; apply Real.exp_monotone; linarith only [(abs_le.mp (H _ u p E _ hz le_rfl (1:Grid c))).1] -- need subscript U
end IV
end Rails
end YM.QCD.Acre
