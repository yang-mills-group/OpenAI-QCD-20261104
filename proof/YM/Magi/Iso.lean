import YM.Magi.Nimbus
import YM.Rebus.Soup
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
variable (L:Side)
set_option quotPrecheck false
local notation "EV"=>measureV L
local notation "Bᵥ"=>run L
open MassiveQCD.Play.Chamber Rift QCD.Bera
lemma rentalV (d n l k m:ℕ)(C':ℝ)(hc:n≤d)(hC:1≤C')(hL:1<L.val):∀ᶠ x in atTop, debt1 l k m (EV n x) ((EV d x)^l) C' (EV (d+1) x) 1 ≤ EV (d+2) x:=by
    let t:=2^l; let v:=l*k+l; let φ:= age l*(2^l:ℕ)
    let Z:=((φ+1)^l*(mead (l*m) C'*(φ*2^t))); let p:ℕ:= (t*l+v*t)
    filter_upwards [goCost L (d+1) (d+2) p Z hL (by omega),(buysV L).eventually_ge_atTop 1] with x h hp
    let s:=EV (d+1) x; have hs:1 ≤ s:=uniformV ..; have hx:0≤ s:= zero_le_one.trans hs
    let q:= EV n x; let q':= EV d x; have hh:1 ≤ q:=uniformV ..; have hh':1≤ q':=uniformV ..
    have hf: φ≥0:=by unfold φ MassiveQCD.Play.Chamber.age; positivity
    have hg: q^(l*k)*q'^l+1≤2*s^v:=by
        apply le_trans (b:=s^v+1) (add_le_add_left ?_ _) ?_; · unfold v; rw [pow_add]; apply mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans hh) (outR L _ _ x hp (by omega)) _) (pow_le_pow_left₀ (zero_le_one.trans hh') (outR L _ _ x hp (by omega)) _) (pow_nonneg (zero_le_one.trans hh') _) (pow_nonneg hx _)
        linarith [show 1 ≤ s^v from one_le_pow₀ hs] -- n
    have hz:= mead_pos (m:=l*m) hC; have ha:(φ*(q^(l*k)*q'^l+1)^t) ≤ φ*(2*s^v)^t:=by gcongr
    unfold debt1 debt0 MassiveQCD.Play.Chamber.face; rw [one_pow,one_mul]
    refine le_trans ?_ h
    calc
        (φ*s^t+1)^l*(mead _ C'*(φ*(q^(l*k)*q'^l+1)^t)) ≤ ((φ+1)*s^t)^l*(mead _ C'*(φ*(2*s^v)^t)):=by gcongr; first| assumption| linarith [show 1 ≤ s^t from one_le_pow₀ hs]
        _= _:=by change ((φ+1)*s^t)^l*(mead (l*m) C'*(φ*(2*s^v)^t))=Z*s^p; unfold Z p; rw [mul_pow,mul_pow 2 (s^v) t,pow_add s (t*l) (v*t),pow_mul s t l,pow_mul s v t]; ring
local notation "Fo"=>fundsL L
abbrev lampK (L:Side)(θ x:ℝ):=fundsL L θ x*(1-(1/2:ℝ))⁻¹
lemma chargeK (L:Side)(θ x:ℝ)(hθ:0 ≤ θ) : 0 ≤ lampK L θ x ∧ lampK L θ x≤2:=by
    have he:0≤ fundsL L θ x:=(fan_pos ..).le
    have hf:fundsL L θ x ≤1:=Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_exp (sq_nonneg _)) (by linarith : -θ ≤0)
    unfold lampK; constructor <;> nlinarith [show ((1-(1/2:ℝ))⁻¹)=2 by norm_num]
-- ep output error dynamics. Assume Λin≤ EV d; Λ_out can scale only by stashes. τP≥uCredit. W err at Thorn choose cutOffV L (1/3) step.V true W. 
local notation "Vd"=>cutOffV L
abbrev spendsK (L:Side)(d:ℕ) (x ε:ℝ):= measureV L (d+2) x*ε + cutOffV L (1/80) x
lemma freedoms (l k m n d:ℕ)(C θ:ℝ)(hL:1<L.val)(hc:1≤C)(hn:n≤d)(hθ:0≤θ)(cb D₀ D₁ Y:ℝ→ℝ)(he:Rate su L (-3) cb)(hz:Rate su L (-(1/32)) Y)(h:Rate su L (-(1/32)) D₀)(h':Rate su L (-(1/32)) D₁)(hV:∀ᶠ x in atTop,0 ≤ cb x ∧ 0 ≤ D₀ x ∧ 0 ≤ D₁ x ∧ 0 ≤ Y x):
    ∀ᶠ x in atTop, let t:=EV d x; let A:=EV n x;
     A^(l*k)*t^l ≤ EV (d+1) x ∧
     ∀ ε:ℝ,0≤ε → ∃ a:ℝ,0≤a∧ tributary l k m (radiusB x) (lampK L θ x) C (t^l) (age l *t^l) A (D₀ x) (D₁ x) (Y x) (Bᵥ x) (cb x) ε≤a ∧ uCredit l m (EV (d+1) x) (Vd (1/3) x) a≤ spendsK L d x ε :=by
    have hx:=powV (rateMeasure L d) l; have h0 := freightRate (n:=k) (l:=l) (m:=m) (C:=C) 2 _ (rateMeasure L n) he (hx.mul_left (age l)) hx hz h h'
    have hu: Rate su L (-(1/32)) (cutOffV L (1/3)) :=(show Rate su L (-(1/3)) (cutOffV L (1/3)) from Rate.power).weaken (by norm_num)
    have hn':= freightP (A:=0) (Z:=0) (l:=l) (k:=m) (Rate.const (L:=L) 1) (rateMeasure L (d+1)) hu h0
    filter_upwards [(buysV L).eventually_ge_atTop 1,goCost L d (d+1) (l*k+l) 1 hL (Nat.lt_add_one _),Delay.shift_pos su L, hV,rentalV L d n l k m C hn hc hL,hn' (-(1/80)) (by norm_num)] with x hp hG hx hv hg hT; intro t A
    have ht:1≤ t:=uniformV ..; have hA:1 ≤ A:=uniformV ..; have he' := hv.1
    refine ⟨?_,fun ε hε=>?_⟩
    · rw [one_mul,pow_add] at hG; exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hA) (outR L n d x hp hn) _) (pow_nonneg (zero_le_one.trans ht) l)) hG
    let u (z:ℝ)(v:ℝ):= tributary l k m (radiusB x) z C (t^l) (age l*t^l) A (D₀ x) (D₁ x) (Y x) (Bᵥ x) (cb x) v
    let T':= EV (d+1) x; obtain ⟨hv₁,hv₂,hv₃⟩:=hv.2; let q:= Vd (1/3) x; have hP:0≤ t:=zero_le_one.trans ht
    refine ⟨u 2 ε,pr _ _ _ _ _ _ _ _ 0 _ 0 _ _ _ _ _ _ hc hA hx.le (pow_nonneg hP _) (mul_nonneg (by unfold MassiveQCD.Play.Chamber.age; positivity) (pow_nonneg hP _)) hε hv₁ hv₂ he' hv₃,tributary2 _ _ _ _ _ _ _ 0 _ _ _ _ _ _ _ _ _ (chargeK L θ x hθ).2 he',?_⟩ -- implicit arg ζ ∃ issue inspect
    have ht : uCredit l m T' q (u 2 0) ≤ cutOffV L (1/80) x:=by change |(1:ℝ)^l*uCredit l m T' q (u 2 0)| ≤ _ at hT; rw [one_pow,one_mul] at hT; exact (le_abs_self _).trans hT
    calc
        uCredit l m T' q (u 2 ε)= uCredit l m T' q (u 2 0)+debt1 l k m A (t^l) C T' 1*ε:=by
             have he:u 2 ε =u 2 0+debt0 l k m A (t^l) C *ε:=linearŪ ..
             rw [he]; simpa only [one_pow,one_mul] using (tariff0 l k m A (t^l) C T' 1 (u 2 0) q ε)
        _ ≤ _:=by unfold spendsK; rw [add_comm _ (cutOffV ..)]; exact add_le_add ht (mul_le_mul_of_nonneg_right hg hε)
end Nimbus
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.Nimbus.freedoms
