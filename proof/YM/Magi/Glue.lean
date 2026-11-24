import YM.Magi.Quartz
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
variable (Pt:ℕ→BudgetPoint)
namespace Nimbus
open MassiveQCD.Rebus Hypnos
open MintV
-- at actual x, launch x1 evaluated from x (at all gates, `run` equals `riseV`). choose ε from heads fixed before.
-- Generic interval march. Forecast profile radius grows **as one ascends**,
-- hence every older test supports projection needed by any later lens in the budget;
-- induction does not price operation flags beyond stocks already paid.
variable (L:Side)
local notation "EV"=>measureV L
local notation "Bᵥ"=>run L
noncomputable abbrev bareK (x:ℝ):=cutOffV L (1/2) x
local notation "Ω"=>cutOffV L
lemma lightsV (x:ℝ)(h:0<Bᵥ x)(d:ℝ):0<cutOffV L d x:=Real.rpow_pos_of_pos h _
lemma marginsV {x y:ℝ}(h:0<Bᵥ x)(hp:Bᵥ x≤ Bᵥ y)(k:ℝ)(hz:0≤k) : Ω k y ≤ Ω k x:=Real.rpow_le_rpow_of_nonpos h hp (neg_nonpos.mpr hz)
lemma peakV {x y:ℝ}(h:0<Bᵥ x)(hp:Bᵥ y ≤2*Bᵥ x)(hx:0<Bᵥ y): Ω (1/2) x ≤ 2*Ω (1/2) y :=by
    have hm:=Real.rpow_le_rpow_of_nonpos hx hp (by norm_num: -(1/2:ℝ) ≤ 0); rw [Real.mul_rpow (by norm_num) h.le] at hm
    unfold cutOffV; apply le_trans ?_ (mul_le_mul_of_nonneg_left hm (by norm_num: (0:ℝ)≤2))
    rw [← mul_assoc]; apply le_mul_of_one_le_left (Real.rpow_nonneg h.le _); rw [Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]; field_simp; rw [← Real.sqrt_eq_rpow]; nlinarith [Real.sq_sqrt (by norm_num:(0:ℝ)≤2)]
lemma agingV (i j:ℕ)(x:ℝ): riseV L (riseV L x i) j = riseV L x (i+j):=by unfold riseV; push_cast; ring
lemma prizeE {x y:ℝ}(h:ticksV L x ≤ ticksV L y) (b:ℕ): EV b x ≤ EV b y:= (pow_le_pow_right₀ (by exact_mod_cast L.pos: (1:ℝ)≤L.val) (Nat.pow_le_pow_left h b))
noncomputable abbrev bloomV (x:ℝ):=run L x^((1/32):ℝ)
lemma caughtV (x y:ℝ)(hp:1 ≤ Bᵥ x) (hV: Bᵥ x≤ Bᵥ y): bloomV L x ≤lantern L y:=by
    have h:(1/32:ℝ) ≤1/8:=by norm_num
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hp h) (Real.rpow_le_rpow (zero_le_one.trans hp) hV (by norm_num:(0:ℝ)≤1/8)) -- lantern ambigu
-- parameter k for top pol initial normalized. if top weights ≲ R^d ~ EV 80 ^d. enough. Radius at output STOP base.K any EV a; allowed. stage major Big clocks unknown.
noncomputable def filmsK (t:ℕ)(z:ℝ)(q:ℕ):= freshS L t z * (4*measureV L 2 z)^q
noncomputable def pitchG (t:ℕ)(z:ℝ)(n q:ℕ):= measureV L t z * (measureV L 2 z)^(n-q)
noncomputable def slipsG (d:ℕ)(z:ℝ)(n q:ℕ):= cutOffV L (1/160) z*(2*measureV L (d+3) z)^(n-q)
lemma clampV (hL:1<L.val)(n m t:ℕ)(C:ℝ)(h:t>m)(hp:1≤C):∀ᶠ x in atTop,∀ q ≤ distV L n x,(C*EV m x)^q ≤ EV (t+n) x:=by
    filter_upwards [goCost L m t 1 C hL h] with x hx q hq
    rw [pow_one] at hx; exact le_trans (pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hp) (zero_le_one.trans (uniformV ..))) hx q) ((pow_le_pow_right₀ (uniformV ..) hq).trans (nexE ..|>.le))
-- reserve constraint t>4 (ratings). choose expansion power `n+k+7(≥Falsifying)`; Ξ total high input.Limit boot.
noncomputable abbrev rentA (b n:ℕ):= b+n+6 -- b wind knob.
abbrev rentD (b c n:ℕ):= rentA b n+c+4
open Suburb
local notation "Vd"=>freshS L
local notation "FV"=>filmsK L
local notation "PtV"=>pitchG L
local notation "Up"=>distV L
lemma livingV (hL:1<L.val)(B n:ℕ) (hB:4≤B): ∀ᶠ z:ℝ in atTop,∀ i≤ distV L n z, FV B z i ≤ Vd (rentA B n) (riseV L z i) :=by
    let d:= rentA B n
    filter_upwards [clampV L hL n 2 3 4 (by omega) (by norm_num),dollsV L n,(buysV L).eventually_ge_atTop 1,lapsV L n,Delay.shift_pos su L,goCost L (B+n+4) (rentA B n) 2 (2:ℝ) hL (by unfold rentA; omega)] with z hz ht hP hf hs hG i hq
    let z':=riseV L z i
    obtain ⟨hr,hh⟩:= hf i hq; have hS:= lightsV L z' (hs.trans_le hr) (1/2)
    have hv: EV B z * (4*EV 2 z)^i ≤ EV (B+n+4) z^2:=by rw [pow_two]; exact mul_le_mul (outR L _ _ z hP (by omega)) ((hz _ hq).trans (outR L _ _ z hP (by omega))) (by have hh:=uniformV L z 2; positivity) ((uniformV ..)|>.trans' zero_le_one)
    unfold filmsK freshS
    calc
        _ = Ω (1/2) z * (EV B z * (4*EV 2 z)^i):=by ring
        _ ≤ 2*Ω (1/2) z' * EV (B+n+4) z^2:= mul_le_mul (peakV L hs hh (hs.trans_le hr)) hv (by have hx:=uniformV L z B; have hy:= uniformV L z 2; positivity) (by positivity)
        _= Ω (1/2) z' * (2*EV (B+n+4) z^2):=by ring
        _ ≤ _:=mul_le_mul_of_nonneg_left (hG.trans (prizeE L (ht _ hq).1 _)) hS.le
-- livingV above at q clock. Needed output radius for i→i+1: pay hQ: ≤fresh ..... CLOCK AT q+1, not q. 
lemma prospectsV (hL:1<L.val)(B n:ℕ) (hB:4 ≤ B):∀ᶠ z:ℝ in atTop, ∀ i < distV L n z, let s:= riseV L z (i+1); FV B z i ≤ Vd (rentA B n) s ∧ EV 1 s * (fiery su s L+FV B z i) ≤ FV B z (i+1):=by
    filter_upwards [livingV L hL B n hB,Delay.shift_pos su L,lapsV L n,priceL L n 1 2 hL (by omega) 1,priceL L n 3 B hL hB 1,aheadΩ L _ (rainingV L hL)] with z h hz hx he hu hf i hi
    let k:=i+1; let t:=riseV L z k
    have hs:= (hx k hi).1
    have h0:= lightsV L z hz (1/2); have hv:1 ≤4*EV 2 z:= by linarith only [uniformV L z 2]
    have ht:0≤FV B z i:=by unfold filmsK freshS; have hx:= uniformV L z B; positivity
    intro q
    refine ⟨?_,?_⟩
    · refine le_trans ?_ (h k hi); change FV B z i≤ FV B z (i+1); unfold filmsK; rw [pow_succ,←mul_assoc]; exact le_mul_of_one_le_right ht hv
    have hQ : fiery su t L ≤ FV B z i:=by
           refine (hf _).trans ?_
           unfold freshS; have hG:1 ≤ EV B z:=uniformV ..; have he1:=hu k hi; rw [pow_one] at he1; unfold filmsK freshS
           have hzq:= marginsV L hz hs (1/2) (by norm_num)
           exact (mul_le_mul hzq he1 (zero_le_one.trans (uniformV ..)) h0.le).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hv))
    change EV 1 t * _≤_
    have he:= he k hi; rw [pow_one] at he
    calc
       EV 1 t*(fiery su t L+FV B z i) ≤EV 1 t*(2*FV B z i):=mul_le_mul_of_nonneg_left (by linarith only [hQ]) (zero_le_one.trans (uniformV ..))
       _ ≤ EV 2 z*(2*FV B z i):=mul_le_mul_of_nonneg_right he (by positivity)
       _ ≤ EV 2 z*(4*FV B z i):=mul_le_mul_of_nonneg_left (by linarith only [ht]) (zero_le_one.trans (uniformV ..))
       _= FV B z (i+1):=by unfold filmsK; rw [pow_succ]; ring
lemma pincerV (hL:1<L.val)(B n a:ℕ):∀ᶠ z:ℝ in atTop, ∀ k≤ distV L n z,∀ i<k, let d:= rentD B a n; let x:=riseV L z (i+1); let t:= PtV a z k (i+1); t ≤ EV d x ∧ t* EV 1 x ≤ PtV a z k i ∧ PtV a z k i ≤ EV d x:=by
   filter_upwards [clampV L hL n 2 3 1 (by omega) le_rfl,dollsV L n, (buysV L).eventually_ge_atTop 1,priceL L n 1 2 hL (by omega) 1,goCost L (a+n+3) (rentD B a n) 2 (1:ℝ) hL (by unfold rentD rentA; omega)] with z hG hf ht hx hA k hq i hi; intro d x t
   rw [one_mul] at hA
   have he(j:ℕ): PtV a z k j ≤ EV d x:=by
       have hx := hG (k-j) (le_trans (Nat.sub_le ..) hq); rw [one_mul] at hx
       apply (le_trans ?_ hA).trans (prizeE L (hf _ (show i+1 ≤ Up n z from by omega)).1 _) -- i shadow! fix
       rw [pow_two]; unfold pitchG
       exact mul_le_mul (outR L a (a+n+3) z ht (by omega)) (hx.trans (outR L _ _ z ht (by omega))) (pow_nonneg (zero_le_one.trans (uniformV ..)) _) (zero_le_one.trans (uniformV ..)) -- fill
   have hM: k-i= k-(i+1)+1:=by omega
   refine ⟨he _,?_,he _⟩
   have hx:= hx (i+1) ((show i+1 ≤ k from hi).trans hq) -- hi < k -> i+1≤ proof
   rw [pow_one] at hx; change EV 1 x ≤ EV 2 z at hx
   unfold t pitchG; rw [hM,pow_succ,←mul_assoc]; apply mul_le_mul_of_nonneg_left hx; exact mul_nonneg (zero_le_one.trans (uniformV ..)) (pow_nonneg (zero_le_one.trans (uniformV ..)) _)
-- relative error and true volume.B flagship
local notation "St"=>slipsG L
lemma pest (hL:1<L.val)(d n:ℕ):∀ᶠ z in atTop,∀ k ≤ distV L n z, ∀ i ≤ k, 0 ≤ St d z k i ∧ St d z k i ≤ Ω (1/320) z ∧ Ω (1/320) z ≤1:=by
   let a:=d+3
   have hh:=MassiveQCD.Rebus.Rift.pmul (Rate.power (G:=su) (L:=L) (a:=-(1/160:ℝ))) (rateMeasure L (d+4+n)); filter_upwards [clampV L hL n (d+3) (d+4) 2 (by omega) (by norm_num), (Work.E09.betaF_growth su L).eventually_gt_atTop 1,hh (-(1/320:ℝ)) (by norm_num)] with z hz h hA k hk i hi
   have hx:0 < Bᵥ z:= lt_trans zero_lt_one h; have hp:= hA; have h0:= lightsV L z hx (1/160); have hf:=uniformV L z (d+3); unfold slipsG; refine ⟨by positivity,(mul_le_mul_of_nonneg_left (hz _ ((Nat.sub_le ..).trans hk)) h0.le).trans ((le_abs_self _).trans hp),Real.rpow_le_one_of_one_le_of_nonpos h.le (by norm_num: -(1/320:ℝ)≤0)⟩
lemma gainingV (hL:1<L.val)(d n:ℕ):∀ᶠ z in atTop,∀ k ≤ distV L n z,∀ i< k, let x:=riseV L z (i+1); spendsK L d x (St d z k (i+1)) ≤ St d z k i:=by
   filter_upwards [priceL L n (d+2) (d+3) hL (by omega) 1, lapsV L n,(Work.E09.betaF_growth su L).eventually_gt_atTop 1] with z h hz ht k hk i hi; intro x; have hi': i+1 ≤ distV L n z:=(show i+1 ≤ k from hi).trans hk; have hx:=h _ hi'; rw [pow_one] at hx
   have hv:= (lt_trans zero_lt_one ht); have h0:= lightsV L z hv (1/160); let V:= St d z k (i+1)
   let W:= EV (d+3) z; have he:1≤ W:= uniformV ..; have hf:0≤ V:=by unfold V slipsG; have h:0 ≤ EV (d+3) z:= zero_le_one.trans he; positivity
   unfold spendsK; have he':Ω (1/80) x ≤ Ω (1/160) z:= (marginsV L hv (hz _ hi').1 (1/80) (by norm_num)).trans (Real.rpow_le_rpow_of_exponent_le ht.le (by norm_num: -(1/80:ℝ) ≤ -(1/160:ℝ)))
   calc
       EV _ x*V + Ω (1/80) x ≤ W*V + Ω (1/160) z :=add_le_add (mul_le_mul_of_nonneg_right hx hf) he'
       _ ≤ W*V + W*V := add_le_add_right ((le_mul_of_one_le_right h0.le (show 1≤(2*W)^(k-(i+1)) from one_le_pow₀ (by linarith only [he]))).trans (le_mul_of_one_le_left hf he)) _
       _ = _:= by unfold V W slipsG; rw [show k-i = k-(i+1)+1 from by omega,pow_succ]; ring
end Nimbus
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.Nimbus.gainingV
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.Nimbus.prospectsV
