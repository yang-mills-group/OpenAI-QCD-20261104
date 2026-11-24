import YM.Bard.Mint
import YM.Clays.Silo
import YM.QCD.Calm.Shoal
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
open Track Depot
namespace MintV
open Finset Real
variable (L:Side)
set_option quotPrecheck false
local notation "qP"=> (↑L.val:ℝ)
local notation "Bᵥ"=>run L
local notation "V"=> highR L
local notation "W" x:arg=> (highR L x+1:ℕ)
lemma opusT : Tendsto (fun x : ℝ=> (W x:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp ((tendsto_atTop_mono (fun i :ℝ=>Nat.le_succ _) ((Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)))))
lemma opusR : Rate su L 0 (fun x=> (W x:ℝ)):=by
     have ht:Rate su L 0 (fun x=> (V x:ℝ)):=by
          refine Rate.bill.compare (Eventually.of_forall fun x=>?_)
          rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (zero_le_one.trans (Delay.bill_ge su L x))]; unfold Delay.bill highR radiusB; linarith only [Nat.ceil_lt_add_one (sq_nonneg (Real.log (betaF su x L))),Nat.cast_nonneg (α:=ℝ) (Nat.ceil (Real.log x^2))]
     simpa only [Nat.cast_add,Nat.cast_one] using ht.add (Rate.const 1)
lemma frontsR :∀ᶠ x in atTop,∀ j, j≤ W x→ Bᵥ x≤ Bᵥ (riseV L x j)∧ Bᵥ (riseV L x j) ≤ 2*Bᵥ x:=by
   let t:= su.slopeConstant*Real.log qP; have ht:0≤t:= Work.E04.shift_nonneg su L
   filter_upwards [((opusR L).mul_right t) 1 (by norm_num)] with x hx i hi; rw [Real.rpow_one] at hx; have hu : (W x:ℝ)*t ≤x+t:=(le_abs_self _).trans hx; have hz:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) ht; have hp:(0:ℝ)≤ i*t:=mul_nonneg (by positivity) ht; change x+t≤x+i*t+t∧ _ ≤ 2*(x+t); change x+t ≤ x+i*t+t ∧ x+i*t+t ≤ _; constructor <;> linarith only [hu,hz,hp]
-- subexp on elongated run.Rates rise
variable {F:ℝ→ℝ}
lemma busR (h:Rate su L a F)(b:ℝ)(hp:a<b):∀ᶠ x in atTop,∀ j ≤ W x, |F (riseV L x j)| ≤ (Bᵥ x)^b:=by
    let p:= (a+b)/2; have he:a<p:=by unfold p; linarith only [hp]
    have hq:p<b:=by unfold p; linarith only [hp]
    filter_upwards [aheadΩ L _ (h _ he),frontsR L,(Rate.const (G:=su) (L:=L) ((2:ℝ)^p)) (b-p) (by linarith), (Work.E09.betaF_growth su L).eventually_ge_atTop 1] with x hx hh hα hv j hj
    let X:=Bᵥ x; let Z:=Bᵥ (riseV L x j); obtain ⟨hR,hH⟩:=hh j hj; apply (hx j).trans; have hX:1 ≤ X:= hv; have hW:0<X:=zero_lt_one.trans_le hX; by_cases ht:0 ≤ p
    · refine (Real.rpow_le_rpow (hW.trans_le hR).le hH ht).trans ?_; rw [Real.mul_rpow (by norm_num) hW.le]; refine (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hα) (Real.rpow_nonneg hW.le _)).trans_eq ?_; rw [← Real.rpow_add hW]; congr 1; ring
    exact (Real.rpow_le_rpow_of_nonpos hW hR (le_of_lt (lt_of_not_ge ht))).trans (Real.rpow_le_rpow_of_exponent_le hX hq.le)
lemma roseR (h:Rate su L a F)(I:ℝ→ℕ)(hI:∀ᶠ x in atTop,I x≤ W x) : Rate su L a (fun x=>F (riseV L x (I x))):=by intro b hb; filter_upwards [hI,busR L h b hb] with x hx hp using hp _ hx
lemma climbT (h:Rate su L a F)(hp:a<0): Tendsto F atTop (𝓝 0):=by rw [Metric.tendsto_nhds]; intro ε he; filter_upwards [h.below hp (ε/2) (by positivity)] with i hi; rw[Real.dist_eq,sub_zero]; exact hi.trans_lt (by linarith only [he])
lemma smallerV (d:ℕ)(a:ℝ)(ha:0<a):∀ᶠ x in atTop,(↑(distV L d x):ℝ)≤a*(V x:ℝ):=by
   filter_upwards [savingsV L a d ha,(Real.tendsto_log_atTop.comp (Work.E09.betaF_growth su L)).eventually_ge_atTop 1] with x hx hp; have h:1≤ Real.log (Bᵥ x):=hp; exact hx.trans (mul_le_mul_of_nonneg_left ((show Real.log (Bᵥ x)≤ _^2 from by nlinarith only [h]).trans (Nat.le_ceil _)) ha.le)
lemma heightR :∀ᶠ x in atTop,∀ j≤ W x, V x ≤ V (riseV L x j)∧(↑(V (riseV L x j)):ℝ)+1≤8*(W x:ℝ):=by
   filter_upwards [frontsR L,(Work.E09.betaF_growth su L).eventually_ge_atTop 2] with x hx hv i hi; let y:=riseV L x i; obtain ⟨hr,hk⟩:=hx i hi; let A:=Bᵥ x; let Z':=Bᵥ y
   have hp:0<A:=lt_of_lt_of_le (by norm_num: (0:ℝ)<2) hv; let t:=Real.log A; have ht:0 ≤ t:=Real.log_nonneg (le_trans (by norm_num: (1:ℝ)≤ 2) hv); have hM:t≤ Real.log Z':= Real.log_le_log hp hr
   have hR: Real.log Z'≤ 2*t:=by
        have h:= Real.log_le_log (hp.trans_le hr) hk; rw [Real.log_mul (by norm_num) hp.ne'] at h; exact h.trans (by change Real.log 2 + t ≤ 2*t; linarith only [show Real.log 2 ≤ t from Real.log_le_log (by norm_num) hv])
   refine ⟨Nat.ceil_le_ceil (pow_le_pow_left₀ ht hM _),?_⟩
   have hX0 : t^2≤ (V x:ℝ):= Nat.le_ceil _
   have hF : (↑(V y):ℝ) ≤ (Real.log Z')^2+1:=(Nat.ceil_lt_add_one (sq_nonneg _)).le
   rw [Nat.cast_add,Nat.cast_one]; exact_mod_cast (by nlinarith only [ht,hM,hR,hF,hX0,pow_le_pow_left₀ (ht.trans hM) hR 2,sq_nonneg t] : (V y:ℝ)+1 ≤8*((V x:ℝ)+1))
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.roseR
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.heightR
