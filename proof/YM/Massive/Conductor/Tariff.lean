import YM.Massive.Conductor.Tunes
import YM.Massive.Beacon.Place
import YM.QCD.Finch.Tar
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Conductor
open Acre
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
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (X:ℂ→ℂ→ Patron.Rail c N I)(Y:ℂ→ℂ→Ruby.Hue c N Ω)
open Ruby Weft High
set_option quotPrecheck false
local notation "Tz"=>P.threshold
variable {b Y₁: ℝ}{s z U:ℂ}
local notation "νT"=> (1/8:ℝ)
open Meridians Rails.Bank
open Massive.Filament Rails.Bank
namespace Quant
variable (L:Side)(G₀:Stage)(N:ℕ)(ε D A3 a3:ℝ)
-- ℓ size fixed. T'=ε means microscopic subsidy. Everything after choosing stride.
abbrev least (L:Side):ℝ:= (L.val:ℝ)/256
abbrev most (L:Side):ℝ:= 16*(L.val:ℝ)
-- all horizon constants BEFORE large L. input Epoch from Beacon
abbrev feeL (G:Stage)(N:ℕ):ℝ:= (2+Pith.jointFee N)*(turnCost G.order G.power)
abbrev feeH (G:Stage):ℝ:=2*(turnCost G.order G.power)
abbrev fossil (G:Stage)(A3 D:ℝ):ℝ:=A3*2*penny G.order*D
abbrev basis (G:Stage)(N:ℕ)(A3:ℝ):ℝ:= fossil G A3 (Carrier.Rental N)
abbrev wear (G:Stage)(N:ℕ)(A3 a3 T ε:ℝ):ℝ:= 1+a3+fossil G A3 T*ε+2*(Fintype.card (Flavor N))
-- leading budget amount.Credit.
abbrev merit :ℝ:=(L.val:ℝ)*basis G₀ N A3*ε+2*wear G₀ N A3 a3 D ε
abbrev refer :ℝ:=(L.val:ℝ)*(basis G₀ N A3+fossil G₀ A3 D)*ε+wear G₀ N A3 a3 D ε
lemma wagePose (G:Stage):0≤turnCost G.order G.power:=by unfold turnCost; positivity
lemma lberry (G:Stage)(N:ℕ):0≤feeL G N:= by have h:= joint_valid N; exact mul_nonneg (by linarith) (wagePose _)
lemma hberry (G:Stage):0≤feeH G:= mul_nonneg (by norm_num) (wagePose _)
lemma cashF (G:Stage)(A3 D:ℝ)(hp:0≤A3)(ht:0≤D):0≤fossil G A3 D:=by
   unfold fossil; positivity [Nimbus.lobby G.order G rfl]
local notation "A4Q"=> wear G₀ N A3 a3 D ε
local notation "pQ"=>basis G₀ N A3
variable (Q₀:ℝ)
-- startup Gate readiness from grow.Requires
structure Prep (G:Stage)(N:ℕ)(A3 a3 D ε Q:ℝ):Prop where
    tilt : 0 ≤ A3
    base : 0 ≤ a3
    wedge : 0 < D
    fuel : 0 < ε
    high : 1 ≤ Q
    funds : Enough N G.order D ε
abbrev lake (L:Side)(Q:ℝ):Prop:= 2*Q^2+2 ≤ least L
structure CarrierL : Prop where
    gives : Prep G₀ N A3 a3 D ε Q₀
    lead : lake L Q₀
    low : feeL G₀ N * merit L G₀ N ε D A3 a3 ≤ D*least L*ε
    high: feeH G₀ * refer L G₀ N ε D A3 a3 ≤ Q₀*D*least L*ε
    stake : 4 *wear G₀ N A3 a3 D ε ≤ least L*ε
    rate : 2 ≤ D*least L*ε
omit L Q₀ in
lemma paCost (hp:0 ≤ A3)(he:0 ≤ a3)(h:0≤ D)(hv:0 ≤ ε):0 ≤ wear G₀ N A3 a3 D ε:=by
    have hr :0 ≤ (Fintype.card (Flavor N):ℝ):= Nat.cast_nonneg _; unfold wear; have hh:=mul_nonneg (cashF G₀ A3 D hp h) hv; linarith
lemma stride (D A B:ℝ)(h:A<B): ∀ᶠ L:Side in atTop,D+L.val*A ≤ L.val*B:=by
   have ht:= sub_pos.mpr h; filter_upwards [Globe.fern_goal.eventually_ge_atTop (D/(B-A))] with d hd; nlinarith only [(div_le_iff₀ ht).1 hd]
-- commit readiness, all patches larger OK. floor lens.
lemma afford_pre (hp:0 ≤ A3)(he:0 ≤ a3): ∃ ε D Q:ℝ,∀ᶠ L:Side in atTop, CarrierL L G₀ N ε D A3 a3 Q:=by
     let f:=feeL G₀ N; let ψ:=basis G₀ N A3;
     let d:ℝ:= max 0 (f*ψ)+1; let D:ℝ:=256*d; have hf:f*ψ<d:=by have h:=le_max_right 0 (f*ψ); unfold d; linarith only [h];
     have hd:0 < d:=by unfold d; have h:=le_max_left 0 (f*ψ); linarith only [h]
     have hp':0<D:=by unfold D; positivity
     obtain ⟨ε,hε,hX⟩:= authorize N G₀.order D; let p:= d*ε; have hh:0 < p:= mul_pos hd hε
     let E:=feeH G₀; let B:ℝ:= E*(ψ+fossil G₀ A3 D)*ε; let Q:= (max 1 (B/p))+1; have hx: 1 ≤ Q:=by have h:= le_max_left 1 (B/p); unfold Q; linarith only [h];
     have hz: B < Q*p:= (div_lt_iff₀ hh).1 (lt_of_le_of_lt (le_max_right 1 (B/p)) (by unfold Q; exact lt_add_one _))
     let g:= wear G₀ N A3 a3 D ε; refine ⟨ε,D,Q,?_⟩
     filter_upwards [stride (f*(2*g)) (f*ψ*ε) p (mul_lt_mul_of_pos_right hf hε),stride (E*g) B _ hz,stride (4*g) 0 (ε/256) (by positivity),stride 2 0 p hh, Globe.fern_goal.eventually_ge_atTop (256*(2*Q^2+2))] with L h1 h2 h3 h4 h5
     refine ⟨⟨hp,he,hp',hε,hx,hX⟩,?_,?_,?_,?_,?_⟩
     · unfold lake least; linarith only [h5]
     · let q:ℝ:= least L; change f*((L.val:ℝ)*ψ*ε+2*g)≤D*least L*ε; unfold p at h1; unfold D least; linarith only [h1]
     · unfold refer; unfold B p at h2; change E*((L.val:ℝ)*(ψ+fossil G₀ A3 D)*ε+g)≤Q*D*((L.val:ℝ)/256)*ε; change E*g+_ ≤ (L.val:ℝ)*(Q*(d*ε)) at h2; rw [show Q*D*((L.val:ℝ)/256)*ε=(L.val:ℝ)*(Q*(d*ε)) from (by unfold D; ring)]; refine Eq.trans_le (show _=_ from (show E*((L.val:ℝ)*(ψ+fossil G₀ A3 D)*ε+g)=E*g+(L.val:ℝ)*(E*(ψ+fossil G₀ A3 D)*ε) from by ring)) h2
     · unfold g at h3; unfold least; linarith only [h3]
     unfold p at h4; unfold least D; linarith only [h4]
-- expose Startup φ. helm resources
variable {L N G₀ ε D A3 a3 Q₀}
abbrev debit (G:Stage)(Z:ℝ):ℝ:= turnCost G.order G.power * Z
lemma stake (hp:Now L P G₀ x)(p:ℝ):meterTurn P p=debit G₀ p:=by unfold meterTurn debit; rw [hp.era.1,hp.era.2.1]
lemma ttl (G:Stage)(L:Side){y:ℝ}(hp:Now L P G y):CorePays P L x (lowNeed L x ε D) (lowNeed L x ε (Rental N)) A3 a3= Nimbus.LNeed L G.order N D ε x A3 a3 ∧ HighPays P L x (lowNeed L x ε D) (lowNeed L x ε (Rental N)) A3 a3= Nimbus.HNeed L G.order N D ε x A3 a3∧ObservePrice P L N x (lowNeed L x ε D) A3 a3= earnsX L N x A3 ((L.val:ℝ)* Nimbus.liftFare G.order L D ε x) a3:=by
   unfold CorePays HighPays ObservePrice snack; rw [hp.era.2.1]; exact ⟨rfl,rfl,rfl⟩
local notation "Gz1"=> G₀.order
local notation "χF"=> Jets.Touch.chip L x
local notation "p₀"=> Nimbus.LNeed L G₀.order N D ε x A3 a3
local notation "p₁"=> Nimbus.HNeed L G₀.order N D ε x A3 a3
local notation "p₂"=> earnsX L N x A3 ((L.val:ℝ)* Nimbus.liftFare G₀.order L D ε x) a3
variable (hj: CarrierL L G₀ N ε D A3 a3 Q₀)
lemma coreBill (L:Side)(I:ℕ)(Y x q:ℝ)(G:Stage)(hp:G.order=I)(W:ℝ):
   q * Brick.fern L * ((L.val:ℝ)*Nimbus.liftFare I L W Y x)= fossil G q W *(Y*Jets.Touch.chip L x):=by
      subst I; unfold Nimbus.liftFare Brick.fern fossil lowNeed; have ht:0<(L.val:ℝ):=by positivity
      field_simp
lemma constS:Nimbus.LMass L G₀.order N ε x A3 a3=King.jelly L x+ ((L.val:ℝ)*basis G₀ N A3 * (ε*χF) + a3*χF):=by
    unfold Nimbus.LMass phaseX basis; rw [mul_assoc (L.val:ℝ) (fossil _ _ _),←coreBill L G₀.order ε x A3 G₀ rfl]; ring
lemma highS : p₁ = King.jelly L x + ((L.val:ℝ)*(basis G₀ N A3+fossil G₀ A3 D)*ε*χF+fossil G₀ A3 D*ε*χF+a3*χF):=by
   unfold Nimbus.HNeed phaseX basis fossil; unfold Nimbus.liftFare lowNeed Brick.fern; have ht :0 < (L.val:ℝ):=by positivity
   field_simp
   ring
-- per-scale monometrics. no input dependence.D.Probe.
variable (hc:0 ≤Jets.Touch.chip L x)(hh:King.jelly L x ≤ Jets.Touch.chip L x)
include hj hc hh
lemma linearCosts : p₀ ≤ merit L G₀ N ε D A3 a3 *χF ∧ p₁ ≤ refer L G₀ N ε D A3 a3*χF ∧ (p₂)≤ wear G₀ N A3 a3 D ε*χF:=by
    let t:= χF; let l:= (L.val:ℝ); let f0:= fossil G₀ A3 D; let p:= f0*ε; let b0:= a3; let U:= basis G₀ N A3; let d := (Fintype.card (Flavor N):ℝ)
    have hp:0≤ d:=Nat.cast_nonneg _; have hv:0≤p:=mul_nonneg (cashF G₀ _ _ hj.gives.tilt hj.gives.wedge.le) hj.gives.fuel.le; let y:=1+b0+p+2*d
    have hy : wear G₀ N A3 a3 D ε=y:=rfl; have hR : Nimbus.LSlop L G₀.order D ε x A3 a3≤ (1+b0+p)*t:=by unfold Nimbus.LSlop phaseX; rw [coreBill (G:=G₀) L _ _ _ _ rfl]; change _ ≤ (1+a3+f0*ε)*χF; change jelly L x+(f0*(ε*t)+a3*t)≤ (1+a3+f0*ε)*t; linarith only [show jelly L x≤ t from hh]
    have hb:1+b0+p≤y:=by unfold y; linarith only [hp]
    have hx:= mul_nonneg hv hc; have ht:=mul_nonneg hp hc; constructor; swap; constructor; swap -- brittle. expand manually below
    · unfold earnsX; change d*(2*_*t)+ Nimbus.LSlop ..≤_; rw [hy]; unfold y; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Brick.fern_one L) hc) hp,hR] -- defeq hc .t syntax
    · rw [highS]; unfold refer; rw [hy]; unfold y; change jelly L x+ (l*(U+f0)*ε*t+p*t+b0*t) ≤ (l*(U+f0)*ε+(1+b0+p+2*d))*t; linarith only [show jelly L x≤t from hh, show 0≤d*t from ht]
    unfold Nimbus.LNeed; rw [constS]; unfold merit; rw [hy]; let r:= Nimbus.LSlop L G₀.order D ε x A3 a3
    change jelly L x+(l*U*(ε*t)+b0*t)+r ≤(l*U*ε+2*y)*t; unfold y; linarith only [show r ≤ _ from hR, show jelly L x≤t from hh,show 0 ≤p*t from hx, show 0≤d*t from ht]
omit hc hh
omit hj in
lemma potential (L:Side):0 < least L:=by unfold least; positivity
omit hj
lemma costsP (L:Side): ∀ᶠ x in atTop, King.jelly L x≤ Jets.Touch.chip L x:=by simpa only [one_mul] using (Calm.Signal.moneyP (A':=King.jelly L) (r:=-1) (Calm.Signal.seed (show Rate su L (-1-1/40) (King.jelly L) from Rate.power) (by norm_num)) (by norm_num) (show 0<(1:ℝ) from zero_lt_one)) -- sig
local notation "xg"=> run L x
local notation "χg"=> Jets.Touch.chip L (run L x)
local notation "τζ"=> Rotary.Spring L x
local notation "pL"=> N
variable {T':Teller su}{Q:ConnectedActivityE6.Target su T'}
-- use names distinct. θ := tau.t; ε purchasing amount. with h=Fuel
abbrev crest (L:Side)(x ε φ:ℝ):ℝ:= φ^2*(ε*Jets.Touch.chip L x)
abbrev coverL (L:Side)(D ε x φ:ℝ):ℝ:=D*least L*crest L (run L x) ε φ
abbrev coverH (L:Side)(D ε x φ Q:ℝ):ℝ:= Q*φ*coverL L D ε x φ
-- Core unconstrained estimates P.order fixed. for T'. Width. Symbol computations Cred.
variable (L N)
local notation "p'"=> Carrier.lowNeed L (run L x) ε D
local notation "r'"=> Carrier.lowNeed L (run L x) ε (Carrier.Rental N)
lemma provesE (G:Stage)(he:CarrierL L G N ε D A3 a3 Q₀)(hh:King.jelly L (run L x) ≤ Jets.Touch.chip L (run L x))(hc:0≤Jets.Touch.chip L (run L x))(R P:BudgetPoint)(hv:Now L R G (run L x))(hr:Now L P G x) (φ:ℝ)(h:0≤φ):
    φ^2*((2+Pith.jointFee N)*meterTurn P (CorePays R L xg p' r' A3 a3))≤ coverL L D ε x φ ∧ φ^3*(2*meterTurn P (HighPays R L xg p' r' A3 a3)) ≤ coverH L D ε x φ Q₀ ∧ 4 * ObservePrice R L N xg p' A3 a3 ≤ (least L)*ε*χg:=by
    obtain ⟨hZ,hQ,hN⟩:= ttl (ε:=ε) (D:=D) (N:=N) (x:=run L x) (A3:=A3) (a3:=a3) G L hv
    rw [hZ,hQ,hN,stake hr,stake hr]; obtain ⟨hZ,hQ,hN⟩:= linearCosts he hc hh; let v:= crest L (run L x) ε φ
    let X:= Nimbus.LNeed L G.order N D ε (run L x) A3 a3; let Y:= Nimbus.HNeed L G.order N D ε (run L x) A3 a3
    have hz: feeL G N * X ≤ (D*least L*ε)*χg:= by nlinarith only [mul_le_mul_of_nonneg_left hZ (lberry G N),mul_le_mul_of_nonneg_right he.low hc] -- lc let
    have hp: feeH G * Y≤ Q₀ * D*least L*ε*χg:= by nlinarith only [mul_le_mul_of_nonneg_left hQ (hberry G),mul_le_mul_of_nonneg_right he.high hc]
    unfold debit coverH coverL crest; unfold feeL at hz; unfold feeH at hp; unfold X at hz; unfold Y at hp
    refine ⟨?_,?_,?_⟩; · nlinarith only [mul_le_mul_of_nonneg_left hz (sq_nonneg φ)]
    · linarith only [mul_le_mul_of_nonneg_left hp (pow_nonneg h 3)]
    exact (mul_le_mul_of_nonneg_left hN (by norm_num)).trans (by nlinarith only [mul_le_mul_of_nonneg_right he.stake hc]) -- infer
-- Quits. local Eye coordinates around y before L? s cost.Serializer.
lemma knots (Φ: Policy Q T'.top N)(A:Prep T'.top N A3 a3 D ε Q₀)(h0: 1 < L.val)(hh:2 ≤ D*least L*ε) : ∀ᶠ x in atTop,0< Jets.Touch.chip L (run L x)→ Jets.Touch.chip L x ≤2*Jets.Touch.chip L (run L x) → ∀ (P:BudgetPoint)(c:Side)(I:Type)[Countable I](φ:ℝ)(X:ℂ→ℂ→Patron.Rail c N I)(s:ℂ),0 ≤ φ→ Fused.Safe (φ:ℂ)→1 ≤ fan L Φ.t x→ Meridians.Seed X P (taxK L x 4) (3/16) (fan L Φ.t x) s→ Quits (faint X 1 (Rotary.Spring L x) φ) P.B (coverL L D ε x φ) (taxK L x 1) (1/8) (fan L Φ.t x) ∧ Quits (Fibre.tail X (Rotary.Spring L x) φ) P.B (coverH L D ε x φ Q₀) (taxK L x 1) (1/8) (fan L Φ.t x):=by
    filter_upwards [mildly (N:=N) L h0 _ (top_chip L) ((event_chip L 1).mono fun i hc=>hc.2.1)] with x hv hZ hC P c I hI φ X s h hp hh' hf
    let r:=Jets.Touch.chip L (run L x); obtain ⟨hk,hK⟩:= hv c P (fan L Φ.t x) hh' I X s (φ:ℂ) hp hf; rw [normS φ h] at hk hK; let v:=(D*least L*ε)*r; have hr : Jets.Touch.chip L x ≤ v:= hC.trans (mul_le_mul_of_nonneg_right hh hZ.le); have hz:= mul_nonneg h h; let p:=φ^2; have he: coverL L D ε x φ=p*v:=by unfold coverL p v crest r; ring
    have h₂:0 ≤ v:= mul_nonneg ((by norm_num : 0≤(2:ℝ)).trans hh) hZ.le
    refine ⟨wattsLoosen _ hk (by rw [he]; exact mul_le_mul_of_nonneg_left hr (sq_nonneg _)), wattsLoosen _ hK ?_⟩ -- bits
    unfold coverH; rw [he]; refine le_trans (mul_le_mul_of_nonneg_left hr (pow_nonneg h 3)) ?_
    have hh3 : φ^3*v ≤ Q₀*(φ^3*v):= le_mul_of_one_le_left (by positivity) A.high; unfold p; nlinarith only [hh3] -- p unfold
structure Weather {N:ℕ}(L:Side)(Q:ConnectedActivityE6.Target su T')(Φ:Policy Q T'.top N)(x t A3 D ε W μ:ℝ):Prop where
    seed : 0 < Jets.Touch.chip L x
    shoot : 0 < Jets.Touch.chip L (run L x)
    warm : Jets.Touch.chip L x ≤2* Jets.Touch.chip L (run L x)
    frame : fan L t x≤ fan L t (run L x)
    dim : fan L t (run L x) ≤2* fan L t x
    root :1 ≤ x
    mint : ∀ (P R:BudgetPoint), Now L P T'.top x → Now L R T'.top (run L x)→ let p:= lowNeed L (run L x) ε D; let r:= lowNeed L (run L x) ε (Rental N); Switch (N:=N) P L x Φ.t (Acre.wage L Φ (run L x)) μ Φ.alpha ∧ 4 * ObservePrice R L N (run L x) p A3 Φ.price ≤ least L*ε*Jets.Touch.chip L (run L x) ∧ mild R L p p (run L x) r p ∧ modulus R p r ∧ ∀ (φ:ℝ) (c:Side),0 < φ → Safe (φ:ℂ)→ Funding Q P R Φ L c x (Rotary.Spring L x) φ (coverL L D ε x φ) (coverH L D ε x φ W) p r A3
lemma allW (Φ:Policy Q T'.top N)(he:CarrierL L T'.top N ε D A3 a3 Q₀)(hp:Billing Φ μ a3 η₀)(h:T'.top.supportExponent=2) (hL:1<L.val): ∀ᶠ x in atTop, Weather L Q Φ x Φ.t A3 D ε Q₀ μ:=by
    have htPrime:= hp.primary
    have hg:= Work.E09.betaF_growth su L; let t:=Φ.t
    filter_upwards [framesC L t htPrime,Finch.dim L t,eventually_ge_atTop (1:ℝ),event_chip L 0,hg.eventually (event_chip L 0),Nimbus.haloFare L ε D A3 Φ hp h he.gives.base he.gives.tilt he.gives.fuel.le he.gives.wedge.le, Meridians.transact (L:=L) Φ h hp, knots L N Φ he.gives hL he.rate,hg.eventually (costsP L),Finch.pegL L,hg.eventually (Carrier.copper L D ε N T'.top.order he.gives.funds)] with x hA hB hX h0 hh hS hY hK hx hz hr -- transp placeholder
    let y:=run L x; let A':=T'.top; refine ⟨h0.2.1,hh.2.1,hz.1,hA.2.2.2,hB,hX,fun P R hxP hxR=>?_⟩
    intro p r; have hw:= hS P hxP; have hXx:=hY P hxP; obtain ⟨hc,hW⟩:= hr R hxR.era.2.1; obtain ⟨hu,hv₁,h₁⟩:= ttl (ε:=ε) (A3:=A3) (N:=N) (a3:=Φ.price) (D:=D) (x:=run L x) A' L hxR
    have hE(φ:ℝ)(hv:0≤φ):= provesE L N A' he hx hh.2.1.le R P hxR hxP φ hv
    refine ⟨hXx,?_,hc,hW,fun φ c hφ hh'=>?_⟩; · rw [hp.tag]; exact (hE 0 (le_refl _)).2.2
    constructor
    · rw [hu,hv₁]; exact hw
    refine ⟨?_,?_,fun I hI X H=> hK hh.2.1 hz.1 P c I φ X φ hφ.le hh' hXx.count H⟩
    · rw [hp.tag]; exact (hE φ hφ.le).1
    rw [hp.tag]; exact (hE φ hφ.le).2.1
end Quant
end YM.QCD.Conductor
#print axioms YM.QCD.Conductor.Quant.allW
