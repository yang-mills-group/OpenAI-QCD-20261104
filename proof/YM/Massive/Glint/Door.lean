import YM.Massive.Glint.Gleam
/-! # Relating the mark-normalized path to nondegenerate calibrated mass signal.

This is NOT PCAC in itself. The reference estimate is on near-zero Fourier momentum of the quadratic terms in the EFFECTIVE fields (State-Wilsonian). PCAC in Massive.Goal makes coherence of the true local fields along with closeness to such readouts a requirement.
-/
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open Grass


open Grass Patron
variable (A: Voice f N) (i₀:Flavor N) (T) (B: Badge P₀ τ R P o χ T U b (run S.L x) r β μ z)


local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Reference
-- one-step transfer along same stopping parameters. No growth frame of F along unchosen schemes.
variable {A3 tol:ℝ}{E:ℕ→SunR Ω}{Xb:ℕ→ℝ}{Ut:ℕ→Towers J.L}
variable (F₀:Flavor N)(M₀:Arrow N) (B:SparkMesh) {M':ℕ→ SparkMesh} (g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:PassageX τ D B M' F₀ χ g Ω E Xb Ut x κ s₀ 1 μ z 1 W' H A' (1/8) o A3 tol)
set_option quotPrecheck false
local notation "f₁"=> towerQ J B n i k
local notation "c₁"=> towerQ J B n (i+1) k
variable {t:ℝ}{Δ:PlaqAxes} {V1 U1 W1:ℕ→ℝ}{Pt:ℕ→BudgetPoint}{D0 a3 Q₀ ξ:ℝ}{Q1:∀ j,Pixel (towerQ J B n j k) N}
-- implicit tol not from above? A3 variables namespace shadow from Bank; outside ended.Bank need declare. see compile.
local notation "xg"=> delay J n i x
local notation "xo"=> delay J n (i+1) x
open Conductor Conductor.Quant High Meridians Ruby High.PrismT Massive.Filament
variable (hZ: Moor t T' B F₀ g Pt E (fun i=> g.costP i+N*Xb i) κ x τ.t D W' k V1 U1 W1 Q1 Δ s₀ tol)
variable (F:∀ j,ℂ→Pixel (towerQ J B n j k) N)
open Aperture Conductor.Quant
open Kin Sway OrbitG MeasureTheory NormedSpace
variable (G₀: Gem c N I)(T: Patron.Rail c N J')
open Finset
open Next.Rank IV Rain
namespace Glint
open High.PrismT Globe Massive.Reading
variable (L1:HaarBudget su)(F':ℂ→Pixel c N)(D':PathData su)
variable {hj:J.Branches T'.bind su}{K1 b₁ b₂ p:ℝ}
variable (Y:∀ j,LanternT (towerQ J B n 0 k) N (towerQ J B n j k)) (hP:Regular L1 (1/2) K1 b₂ T' Q B F₀ x κ τ g Pt E (fun i=> g.costP i+N*Xb i) D W' k V1 U1 W1 Q1) -- common θ fix
variable (hk: CarrierL J.L T'.top N ε D0 A3 a3 Q₀)(hC:Sharp.Purer T' J Ω N x τ.t a d Λ κ ε D0 b₁)(hp: Gallery T' J n k B N V1 W1 Q1 Y hj)
variable (hw: Fueled T' B F₀ M₀ V1 U1 g Pt E τ.t x ε D0 k Y p v)(ht:Sharp.Attendance F₀ M₀ B Y τ.t D0 ε b₁ b₂ w v E Pt T' V1 U1 L1 x g)
open Sharp
local notation "sY"=>ShapeX B Y M₀.tip v
local notation "qX"=> gainsW B Y M₀ τ.t x
local notation "φ"=>Rotary.chartR
variable (F0:HaarBudget su)
include hP hp hk hw ht hC
local notation "zq"=> scent (c:=c) U.Z.page P D' T'.top.clip α 0 N
local notation "sp"=> positiveAnswer
omit hP hp hk hw ht hC in
private lemma cross (q:ℝ)(X:ℂ)(z:ℝ)(h:‖X-(q:ℂ)‖ ≤ r)(h1:‖X- (z:ℂ)‖≤p): |q-z|≤r+p:=by
    rw [← Real.norm_eq_abs,← Complex.norm_real, Complex.ofReal_sub]; exact (norm_sub_le_norm_sub_add_norm_sub (q:ℂ) X z).trans (add_le_add ((norm_sub_rev ..).trans_le h) h1)
set_option maxHeartbeats 500000 in
lemma approach (hL:1<J.L.val) (h₀:FitLevel L1 τ B F₀ g K1 b₂ Pt E (fun i=>g.costP i+N*Xb i) κ x D W' r k)(ht':0 < σ)(hN:0<n)(hm:p=Quant.crest J.L x ε σ)(hA:∀ b:Flavor N,Air (Pt n) J.L F₀ b τ.t x (Requests (N:=N) D0 ε J x) r Ω (passportM J.J J.order_cut) (towerQ J B n n k)):
 ∀ b, let Q:= (money τ.t p J.L x); let X:= flagW (fumes b ((ShapeX B Y M₀.tip v n w) 1));
       ‖planeProbe (Cove.light _ ∘ ShapeX B Y M₀.tip v n w) b- (X:ℂ)‖≤r ∧ |X-sp J x κ τ.t-attendance x w*M₀.tip b*Q|≤ 2*r + (σ*D0*Q):=by
    have hf:=ping B hj Y hp (show n ≤n from le_rfl) M₀.tip v; have hb: delay J n n x=x:=by simp [delay,tallyK]
    let q:=money τ.t p J.L x; have hg: v*(qX n)=p:= hw.2.2.1
    obtain ⟨t,hU,hV,hM,H⟩:= gleam (r:=r) F₀ M₀ B g L1 Y hP hk hC hw ht hL (show n≤ n from le_rfl) (hb.symm ▸ hA); let p0:=sp J x κ τ.t; have hv: U1 n=p0:=by obtain h:= hP.finish.2; simpa only [p0,rangeG,hb] using h
    have ht'':t=σ:= by
       have hp:0<ε*Jets.Touch.chip J.L x:=mul_pos hk.gives.fuel (hC.pos x le_rfl).2.2.1; unfold Quant.crest at hm; rw [hb,hg,hm] at hM; have hx:=mul_right_cancel₀ hp.ne' hM; nlinarith only [hx,hU,ht']
    intro b; have hp:= H b; rw [hb,hg,ht''] at hp; let X:= flagW (fumes b (Q1 n 1)); have hz: |X - p0| ≤2*r:= by
       have h:= (h₀.attend (1/2) V1 U1 W1 Q1 hP n le_rfl).2 hN b; rw [hv] at h;
       have hn:=hp.zeroL; rw [hf] at hn; exact (cross X _ p0 hn h).trans_eq (by ring)
    intro Q X₀; obtain he:= hp.worthL; rw [hf] at he; refine ⟨hp.glassL,?_⟩; obtain ⟨h1,h2⟩:= abs_le.mp he; obtain ⟨h3,h4⟩:= abs_le.mp hz; change |X₀-p0-attendance x w*M₀.tip b*Q|≤ _; change - (_*Q)≤X₀-X-_ at h1; change X₀-X- _ ≤ _*Q at h2; apply abs_le.mpr; constructor <;> linarith only [h1,h2,h3,h4]
omit hP hp hk hw ht hC
abbrev Value (u:ℝ):=u/16
structure KeyL (J:Patch)(ε D κ σ:ℝ) :Prop where
 bounded : 64*ε*σ^2* (J.L.val:ℝ) ≤ κ
 paid : σ*D ≤ 1/256
 room: 0 < σ
 kept: σ ≤ 1/4
lemma door (hE:0<ε)(hD:0<D0)(hκ:0<κ) : ∃ σ:ℝ, KeyL J ε D0 κ σ:=by
    let p:ℝ:= min (κ/(64* ε*J.L.val)) (1/4); let s:=min p ((1/256)/D0); have hp:0<p:=lt_min (by positivity) (by norm_num); have ha:0<s:=lt_min hp (by positivity); have hx:s≤ 1/4:=(min_le_left ..).trans (min_le_right ..); refine ⟨s,⟨?_,(le_div_iff₀ hD).mp (min_le_right ..),ha,hx⟩⟩; have hr:= (le_div_iff₀ (by positivity : 0<64*ε*J.L.val)).mp (show s≤_ from (min_le_left p ((1/256)/D0)).trans (min_le_left ..)); apply le_trans _ hr; nlinarith only [mul_le_mul_of_nonneg_left (show s^2 ≤ s from (by rw [pow_two]; exact mul_le_of_le_one_left ha.le (by linarith only [hx]))) (show 0≤64*ε*J.L.val from by positivity)]
include hP hp hk hw ht hC
omit hP hp hk hw ht hC in
lemma keyLoad (hT:KeyL J ε D κ t)(hz:0<Jets.Touch.chip J.L x)(hx:p=Quant.crest J.L x ε t): 8*money τ.t p J.L x ≤ sp J x κ τ.t:=by
    let X:=fan J.L τ.t x; let f:=(J.L.val:ℝ); have hh:0<X:=fan_pos ..; have hF: 0<f:=by unfold f; positivity
    rw [hx]; unfold money positiveAnswer roofK Emax Quant.crest; change 8*(t^2* _ / X^2) ≤ _/(2*X)^2/f*_ ; field_simp; nlinarith only [show 64*ε*t^2* f ≤ _ from hT.bounded]
omit hP hp hk hw ht hC in
lemma distinct {V:Flavor 6→ℝ}(hq:0<q)(hT:8*q≤p)(hA: v∈Set.Icc (1/8:ℝ) (1/2)) (hp:∀ i:Flavor 6, |V i - p - v*fork.tip i*q| ≤ q/64) : (∀ i,Value q≤V i) ∧(∀ i j: Flavor 6,i≠j→ Value q ≤ |V i - V j|)∧(∀ i, V i ≤2*p) :=by
    have ht(i:Flavor 6): |v*fork.tip i*q|≤5*q:=by
        have hz: ‖v‖ ≤1:= by rw [Real.norm_of_nonneg (by linarith only [hA.1])]; linarith only [hA.2]
        rw [abs_mul,abs_mul,abs_of_pos hq]; gcongr; exact le_trans (mul_le_mul hz (fork.bound i) (abs_nonneg _) zero_le_one) (by rw [one_mul])
    unfold Value; have hs (i j:Flavor 6)(h:i≠j):2≤|fork.tip i-fork.tip j|:=by fin_cases i<;> fin_cases j<;> first | exact False.elim (h rfl) | norm_num [fork,rayU] -- watch costs
    have hm (i:Flavor 6): p-6*q≤V i ∧ V i ≤p+6*q:= by obtain ⟨hæ,hl⟩:= abs_le.mp (ht i); obtain ⟨h1,h2⟩:= abs_le.mp (hp i); constructor <;> linarith only [hæ,hl,h1,h2,hq];
    refine ⟨fun i=>by linarith only [(hm i).1,hq,hT],fun i j h=>?_ ,fun i=>by linarith only [(hm i).2,hT,hq]⟩; obtain ⟨h1,h2⟩:=abs_le.mp (hp i); obtain ⟨h3,h4⟩:=abs_le.mp (hp j); have hz:= (div_pos (show (0:ℝ)<1 from zero_lt_one) (by norm_num : (0:ℝ)<8)).trans_le hA.1; rw [le_abs]; rcases le_abs.mp (hs i j h) with h|h; · left; nlinarith only [h1,h2,h3,h4,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hz.le) hq.le,mul_le_mul_of_nonneg_right hA.1 hq.le,hq]
    right; nlinarith only [h1,h2,h3,h4,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hz.le) hq.le,mul_le_mul_of_nonneg_right hA.1 hq.le,hq]
omit hP hp hk hw ht hC
end Glint
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Glint.approach
#print axioms YM.QCD.Acre.Rails.Reference.Glint.distinct
