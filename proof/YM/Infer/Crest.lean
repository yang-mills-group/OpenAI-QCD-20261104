import YM.Differ.Humming
import YM.Profiles.Dawn
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
namespace Counter
open Work.E09 Next.Rank -- unknown
-- elementary numerical gear for all expiry & pack. enters after.L before pad. pressure clocks.
variable (L:Side)(u:ℝ)
namespace Hymn
open Bounce
variable {D:ℕ}
-- α halo max S growth.Prior.Blue.A.D stamp valuations.U
lemma spark {a b:ℝ}(h: Bounce.Ticket a b (Kit.slope L)): 1+2*a ≤ 3* (L.val :ℝ):=by
    let f:= Kit.slope L; have h0:0<f:=h.moves; have hu:0<Real.sqrt f:=Real.sqrt_pos.2 h0; have hB: f ≤1:=h.bounded; have hP:f ≤ Real.sqrt f:=by nlinarith only [Real.sq_sqrt h0.le,hB,h0,hu]
    have ht: a*Real.sqrt f ≤1 := (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg a)) (Real.sqrt_nonneg f)).trans (h.shrinks.trans (by norm_num)); have ha:=h.starts
    let t:ℝ:=(L.val:ℝ); have hv : a ≤ Real.sqrt t := by
        rw [show Real.sqrt t= _ from (show Real.sqrt t =1/f from by unfold f Kit.slope t; simp), le_div_iff₀ h0]; exact (mul_le_mul_of_nonneg_left hP (zero_le_one.trans ha)).trans ht
    have hj:=Real.sq_sqrt (x:=t) (by unfold t; positivity); change _≤ 3*t; have hq: 1 ≤ t:=by unfold t; exact_mod_cast L.property
    nlinarith only [hv,hj, Real.sqrt_nonneg t,hq,ha]
open Economies
local notation "vΓ"=> (D:ℝ)/2
local notation "pT"=> pitchD D
variable (q:ℕ→ℝ)(hq:∀ᶠ i in atTop,Bounce.Ticket (q i) (q (i+1)) (Kit.slope (A.spacing i)))
include hq
-- y:world.T.g cost ≤ exp(c*log(b)) if dim.C.Energy zn scaled.
lemma vanish (t:ℕ)(Z:ℝ)(hT: 1 ≤ Z) : Tendsto (fun i:ℕ=> Real.exp ((vΓ+1/16)* A.measure i)*(damping P₀ A D i t * ((1+2*q i)* Z))) atTop (𝓝 0):=by
    let M (i:ℕ):= Track.measure A i; let r (i:ℕ):=(vΓ+1/16)*M i; let f (i:ℕ):= damping P₀ A D i t; let u (i:ℕ):= Real.exp (r i); let v:ℝ:=1/16
    let z:= Real.exp (pT*M t)*(3*Z); let S (i:ℕ):= Real.exp (-(2*v)*M i)
    have hp: Tendsto S atTop (𝓝 0):= by
         apply Real.tendsto_exp_atBot.comp; exact Filter.tendsto_neg_atTop_atBot.comp (A.long.const_mul_atTop (show 0< (2:ℝ)*v from by unfold v; norm_num)) |>.congr' (Eventually.of_forall fun i=> by simp only [Function.comp_apply, neg_mul]; rfl)
    have hz: Tendsto (fun i=> z*S i) atTop (𝓝 0):=by simpa using hp.const_mul z
    let T (i:ℕ):=u i*(f i*((1+2*q i)*Z)); have hh: ∀ᶠ i in atTop,0≤ T i∧ T i≤ z*S i:=by
          filter_upwards [hq,anyRay P₀ A v (by unfold v; norm_num)] with i hi ht
          let L:= A.spacing i; have he := spark L hi; have hm: (L.val:ℝ)≤ Real.exp (v*M i):= by nth_rw 1 [← Real.exp_log (show 0 <(L.val:ℝ) from by positivity)]; exact Real.exp_monotone ht
          have ha:0≤ T i:=by unfold T u f damping; positivity [hi.starts]
          refine ⟨ha,?_⟩; unfold T; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (he.trans (mul_le_mul_of_nonneg_left hm (by norm_num))) (zero_le_one.trans hT)) (Real.exp_nonneg _)) (Real.exp_nonneg _)) (le_of_eq ?_)
          unfold z; rw [show u i*(f i*(3*Real.exp (v*M i)*Z))= (u i*f i*Real.exp (v*M i))*(3*Z) from by ring]; unfold u f S r damping M v pitchD; rw [mul_right_comm (Real.exp _) (3*Z),←Real.exp_add, ← Real.exp_add,←Real.exp_add]; ring_nf
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz (hh.mono fun _ h=> h.1) (hh.mono fun _ h=>h.2)
end Hymn
end Counter
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Counter.Hymn.vanish
