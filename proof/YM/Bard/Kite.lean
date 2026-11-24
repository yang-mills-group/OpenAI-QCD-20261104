import YM.Bard.Mint
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
local notation "ck"=>ticksV L
local notation "Bᵥ"=>run L
local notation "Ω"=>lapV L
local notation "pL"=> (↑L.val:ℝ)
local notation "EV"=>measureV L
local notation "τ"=>distV L
-- algebra rents; receipts cut.Full clock d'.
lemma χone (x:ℝ)(k:ℕ):0 < EV k x:=zero_lt_one.trans_le (uniformV ..)
lemma nexE (a b:ℕ)(x:ℝ): (EV a x)^(τ b x)=EV (a+b) x:=by unfold measureV distV; rw [←pow_mul,pow_add]
lemma soarCost (d a b k:ℕ)(hb:a<b)(hL:1<L.val):∀ᶠ x in atTop,(d:ℝ)*(EV a x)^k ≤ EV b x:=by
    rcases Nat.eq_zero_or_pos a with ha|ha; swap
    · filter_upwards [(tonicV L hL ha).eventually_ge_atTop (d:ℝ),priceL L 1 a b hL hb (k+1)] with x hx ht; have hh:=ht 0 (Nat.zero_le _)
      have he: riseV L x 0=x:=by simp [riseV]
      rw [he,pow_succ,mul_comm] at hh; exact (mul_le_mul_of_nonneg_right hx (pow_nonneg (χone ..|>.le) _)).trans hh
    subst a; have h(x):measureV L 0 x=pL:=by simp [measureV,distV]
    simp_rw [h]; exact (tonicV L hL hb).eventually_ge_atTop _
lemma goCost (a b k:ℕ)(C:ℝ)(hL:1<L.val)(hb:a<b):∀ᶠ x in atTop,C*(EV a x)^k ≤ EV b x:=by filter_upwards [soarCost L ⌈C⌉₊ a b k hb hL] with x hp using (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (pow_nonneg (χone ..|>.le) _)).trans hp
lemma outR (d k:ℕ)(x:ℝ)(h:1≤ ck x)(hi:d≤k): EV d x ≤ EV k x:=pow_le_pow_right₀ (by exact_mod_cast (show 1≤ L.val from L.pos)) (pow_le_pow_right₀ h hi)
lemma escapeR (d k:ℕ)(x y:ℝ)(hx:ck x≤ck y)(hp:1 ≤ ck y)(hi:d≤k): EV d x ≤ EV k y:=(show EV d x≤EV d y from pow_le_pow_right₀ (by exact_mod_cast L.pos:1 ≤ pL) (Nat.pow_le_pow_left hx d)).trans (outR L d k y hp hi)
lemma curtailV (d:ℕ)(A:ℝ)(h:1<L.val):∀ᶠ x in atTop,∀ i≤τ d x, fan L A (riseV L x i) ≤ EV 3 x:=by
   let u:=Real.log pL; have hu:0<u:= Real.log_pos (by exact_mod_cast h); let C:= |A| * 16
   filter_upwards [dollsV L d,aheadΩ L _ ((livesV L).eventually_ge_atTop 0),(tendsto_natCast_atTop_atTop.comp (buysV L)).eventually_ge_atTop (C/u)] with x hx ht hs i hi
   let y:=riseV L x i; let k:=ck x; have hp: (Ω y)^2 ≤ (4*(k:ℝ))^2:=pow_le_pow_left₀ (ht i) ((hx _ hi).2) 2; have hv': C ≤ (k:ℝ)*u:= (div_le_iff₀ hu).1 hs
   apply (Real.log_le_log_iff (fan_pos ..) (χone ..)).mp; change Real.log ((Real.exp ((Ω y)^2))^ A) ≤ _; rw [Real.log_rpow (Real.exp_pos _),Real.log_exp]; unfold measureV; rw [Real.log_pow]; change A* _≤ (↑(k^3):ℝ)* u; push_cast; nlinarith only [mul_le_mul (le_abs_self A) hp (sq_nonneg _) (abs_nonneg A), show |A| * 16 ≤ ↑k *u from hv',mul_le_mul_of_nonneg_right hv' (sq_nonneg (k:ℝ))] -- C unfold.CΛ
lemma solar_size (A:ℝ→ℝ)(hp:Rate su L a A)(ha:a<b) (n:ℕ)(hd:1<L.val) : ∀ᶠ x in atTop,(EV n x)*|A x| ≤ Bᵥ x^b:=by
   have hV:= (rateMeasure L n).mul hp; filter_upwards [hV b (by simpa using ha)] with x hx; simpa only [abs_mul,abs_of_nonneg (show 0 ≤EV n x from χone ..|>.le)] using! hx
-- helpers on plateau.
lemma atickV (A:ℝ→ℝ)(hp:Rate su L a A)(ha:a<b)(hb:b ≤ 0) (n:ℕ) :∀ᶠ x in atTop,∀ i≤τ n x, |A (riseV L x i)| ≤ Bᵥ x^b:=by
    filter_upwards [lapsV L n,Delay.shift_pos su L,aheadΩ L _ (hp b ha)] with x hx hv ht i hi using (ht i).trans (Real.rpow_le_rpow_of_nonpos hv ((hx i hi).1) hb)
lemma fareS (α:ℝ)(hb:0 < α)(n k:ℕ):∀ᶠ x in atTop,(EV k x)^(τ n x) ≤ Bᵥ x^α:=by
    simp_rw [nexE]; filter_upwards [rateMeasure L (k+n) α hb] with x hx; exact (le_abs_self _).trans hx
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.curtailV
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.atickV
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.fareS
