import YM.VStages.TariffW
import YM.Massive.Conductor.Livery
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
variable {c f C F L:Side} {J:Patch} {j k kP nP n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
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
-- funding to bounding: step concentration & observant
variable {T':Teller su}{Q: ConnectedActivityE6.Target su T'} (Φ:Policy Q T'.below N)(Y:Code c N) (F:ℂ→ Pixel c N)
variable (A₀: Arrow N) -- disambiguate
local notation "xg"=>run L x
local notation "tᵒ"=>fan L Φ.t x
local notation "hᵍ"=> Acre.wage L Φ (run L x)
local notation "tG"=>fan L Φ.t (run L x)
local notation "κG"=>Rotary.Spring L x
variable {S0 φ D0 ε εout Dout A3 a3 Q₀ R0:ℝ}
-- D.Tool requires positivity & mass anchor ≈m within; start Stigma.Certificate via head pinning.
-- algebra helper local scaling. Numeric.Pos.Int law.
variable (L)
variable {G:Stage}{K:KernelChoices}
structure FogLeaf (Φ:Policy Q T'.below N)(P R:BudgetPoint)(c L:Side)(x A3 ε D s:ℝ) :Prop where
    billG : (Rotary.Spring L x)*(Finch.fare Φ.alpha P.B*(meterTurn P (CorePays R L (run L x) (lowNeed L (run L x) ε D) (lowNeed L (run L x) ε (Rental N)) A3 Φ.price))) ≤ (c.val:ℝ)/2*(least L *(ε*Jets.Touch.chip L (run L x)))
    near : (L.val:ℝ)/2≤ s
    high : s ≤2*(L.val:ℝ)
abbrev rimV (G:Flight j kP)(h:f.val=c.val*G.L.val):ℝ:= flagW (Garden.barP G h*proton G h)
def StationY (Φ: Policy Q T'.below N)(j kP:ℕ)(L c:Side)(ε A3 D x:ℝ) :Prop := ∀ (P R:BudgetPoint)(f:Side)(S:Flight j kP)(h:f.val=c.val*S.L.val),S.L=L→ Now L P T'.below x → Now L R T'.below (run L x) → FogLeaf Φ P R c L x A3 ε D (rimV S h)
lemma leavesY (p:Plan j)(h:4≤j)(h':4≤kP)(hh:0<ε)(hK:WeatherY L Q Φ x Φ.t A3 D Dout ε Q₀ μ):∀ᶠ c in atTop, StationY Φ j kP L c ε A3 D x:=by
    let t:=T'.below; let p0:= Nimbus.LNeed L t.order N D ε (run L x) A3 Φ.price
    let W:=κG*(Finch.fare Φ.alpha (highR L x)*(debit t p0)); let M:=least L*(ε*Jets.Touch.chip L (run L x)); have hΦ: 0 < M := mul_pos (potential L) (mul_pos hh hK.shoot)
    have hp₀:0 < (L.val:ℝ):=by positivity
    filter_upwards [Globe.fern_goal.eventually_ge_atTop (2*W/M),Finch.earnings p (half_pos hp₀) h h' L] with c hv hZ; intro P R f S hi hx hP hR; have hz:= hZ.2 S hx f hi; obtain ⟨h1,h2⟩:= abs_le.mp hz
    refine ⟨?_,by unfold rimV; linarith only [h1],by unfold rimV; linarith only [h2,hp₀]⟩; rw [(ttl _ L hR).1,stake hP,hP.ball]; change W≤(c.val:ℝ)/2*M; linarith only [(div_le_iff₀ hΦ).1 hv]
-- Putting proofs
variable (S0:ℝ) (R:BudgetPoint) (hp:Now L P T'.below x)(hR:Now L R T'.below (run L x))(hL: FogLeaf Φ P R c L x A3 ε D S0)
variable (hj: PriceCross L T'.below N ε D A3 a3 εout Dout Q₀)(he:WeatherY L Q Φ x Φ.t A3 D Dout ε Q₀ μ)
local notation "p'"=> Carrier.lowNeed L (run L x) ε D
local notation "r'"=> Carrier.lowNeed L (run L x) ε (Rental N)
local notation "ΦL"=> CorePays R L (run L x) (lowNeed L (run L x) ε D) (lowNeed L (run L x) ε (Rental N)) A3 Φ.price
local notation "ΦS"=> ObservePrice R L N (run L x) (lowNeed L (run L x) ε D) A3 Φ.price
local notation "κi"=> hear L F Φ.t x
-- charge Polit.Zero when triggering call. read m* etc. use numerical pre-aligned around. Future Π Orientation.Holo
include hp hR hL he hj
variable {V:ℕ} {m₀: Flavor N → ℝ}
include Φ
lemma growthPoseY (hv:0<φ) (h:1/2 ≤ v)(hz:v≤2) (f: Flavor N)(hq:m₀ f=fieldRent φ d)(hh:ε*Jets.Touch.chip L (run L x)>0)(hm:|tG^2*d -crest L xg ε φ| ≤ crest L xg ε φ/2)(hβ:‖hear L F Φ.t x f - φ^2*κG*v^2*((tᵒ)^2*(m₀ f*S0))‖ ≤ φ^2*κG*v^2*((tᵒ)/hᵍ)^2*ΦS) (hL':1<L.val): let M:=crest L xg ε φ; least L*M ≤ κi f ∧ κi f ≤ most L*M :=by
    obtain ⟨hQ,hΦ,hX⟩:=he.mint P R hp hR; let y:= run L x; let W:=tᵒ; let H:=hᵍ; let φ₀:=φ^2; let Q:= least L
    intro M; have hW:1 ≤ W:=hQ.count; have hH:2*W≤ H:=hQ.steer; have hx:0 < ε * Jets.Touch.chip L xg:= mul_pos hj.gives.fuel he.shoot
    obtain ⟨hq',hG,hξ,hΓ,hC,-⟩:= Rotary.spring L hL' x he.root; have hz':W≤H:=by linarith
    have hpZ:0 ≤ v:=by linarith only [h]
    have hZ:0< M:= mul_pos (sq_pos_of_pos hv) hx
    rw [hq] at hβ; have hS:= signal_prop tG S0 W d M L.val φ κG v hv hξ (hΓ.trans hC).le h hz (fan_pos ..) he.frame he.dim (by positivity) hL.near hL.high hZ hm;
    let D':= φ^2*κG*v^2*((tᵒ)^2*(fieldRent φ d*S0)); have hh:= cherish (V:=W) (T:=H) (ΦS) (Rotary.Spring L x) φ v hz' (zero_le_one.trans hW) (by linarith) hΦ hG.le (hΓ.trans hC).le hpZ hz (by nlinarith only [hx, mul_pos (potential L) hh] : 0 ≤ least L * ε * Jets.Touch.chip L xg)
    have hr: φ^2*(least L*ε*Jets.Touch.chip L y)=Q*M:=by unfold Q M crest; ring;
    obtain ⟨ht,hS'⟩:= abs_le.mp ( (show |hear L F Φ.t x f - D'| ≤ Q*M from hβ.trans hh|>.trans hr.le))
    let T:=κi f; let ηl :ℝ:= L.val
    change ηl/128*M≤ D' ∧ D' ≤ 12*ηl*M at hS; change _ ≤ T -D' at ht; change T-D' ≤_ at hS'; change least L*M ≤ T ∧ T ≤ 16*ηl*M; have hp :Q=ηl/256:= rfl; rw [show least L=Q from rfl]; have hy:0≤ ηl*M:=by unfold ηl; positivity
    rw [hp] at ht hS' ⊢; constructor <;> linarith only [ht,hS.1,hS.2,hS',hy] -- nlin
-- growth unconditional at least.Rent formula exact simplifies higher.Fh.PS.
local notation "gg"=> Fin (N+1)
variable (Y₀: Code f N) (K':Grid c→ℝ)(T1:St c)(b':Flavor N)
set_option maxHeartbeats 900000
variable (hv:0<φ)(hz:1/2 ≤ v)(hw:v≤2)(hZ:∀ i:Flavor N,|(fan L Φ.t (run L x))^2 *Y₀.focus i - Quant.crest L (run L x) ε φ*A₀.tip i| ≤ Quant.crest L (run L x) ε φ/2)
local notation "S₁"=>κi A₀.head
variable (h0:1<L.val)
include h0 hv hz hw hZ
lemma stepY (hA: Pend L F P K' T1 x Φ.t Φ.alpha (meterTurn P ΦL) (coverL L Dout ε x φ) (coverH L Dout ε x φ Q₀) φ κG v hᵍ ΦS S0 (Carrier.rentalM Y₀ φ) b') : LadderStep L F P A₀ b' K' T1 x Φ.t εout Dout (crest L xg ε φ):=by
   let s:=xg; let M:= crest L xg ε φ; let W:= least L; let κ:=εout*Jets.Touch.chip L x; let h:=A₀.head; let H:= hear L F Φ.t x A₀.head
   obtain ⟨Y',hD,hΨ⟩:= hA.push; have hm := hZ A₀.head; rw [A₀.has_one,mul_one] at hm; have hx:0<ε*Jets.Touch.chip L s:=mul_pos hj.gives.fuel he.shoot; obtain ⟨h1,h2⟩:=growthPoseY L Φ F S0 R hp hR hL hj he hv hz hw h (d:=Y₀.focus h) rfl hx hm (hΨ h).2 h0
   change W*M≤H at h1; change H ≤ most L*M at h2
   have hκ: 0< κ:=mul_pos hj.outE he.seed; have hF:0<Q₀:=zero_lt_one.trans_le hj.gives.high; have hh:0< M:= mul_pos (sq_pos_of_pos hv) hx; have hH :0<H:= (mul_pos (potential L) hh).trans_le h1
   let ψ:= √(H/κ); have hy : 0<ψ:=Real.sqrt_pos.2 (by positivity); have hW : H=ψ^2*κ:=by unfold ψ; rw [Real.sq_sqrt (by positivity),div_mul_cancel₀]; exact hκ.ne'
   refine ⟨fun b e hb=>hb.symm ▸ h1,h2,fun h=>?_⟩; refine ⟨hH,h,⟨Y',hD.desk,hD.wing,?_,ψ,hy,hW,?_⟩⟩
   · intro i; have hB := mul_le_mul_of_nonneg_left hL.billG (sq_nonneg φ);
     have h₁ : (c.val:ℝ)* |(hear L F Φ.t x i) - (tᵒ)^2* Y'.focus i| ≤ (c.val:ℝ)/2*(least L*M):= (hΨ i).1.trans (by unfold M crest; linarith only [hB]);
     have hy :κi i= (κi A₀.head)*A₀.tip i:= h i
     rw [abs_sub_comm, ←hy]; change |κi i-(tᵒ)^2* Y'.focus i|≤ H/2; change (c.val:ℝ)*_ ≤ (c.val:ℝ)/2*(W*M) at h₁; exact le_of_mul_le_mul_left (by linarith only [mul_le_mul_of_nonneg_left h1 (show 0≤(c.val:ℝ) from by positivity),h₁] : (c.val:ℝ)* _ ≤ (c.val:ℝ)* (H/2)) (by positivity)
   have hxV : Q₀*φ ≤ ψ:=by
      let d:= Jets.Touch.chip L x; let r:=Jets.Touch.chip L s; have hx:= he.warm; have hh2: Q₀^2*κ ≤ W*(ε*r):=by
            have h₂ := mul_le_mul_of_nonneg_left hx hj.outE.le; change κ ≤ εout * (2*r) at h₂; have hB:= hj.lead; change (2*Q₀^2+2)*εout ≤ W*ε at hB
            nlinarith only [mul_le_mul_of_nonneg_right hB (show 0 ≤ r from he.shoot.le),mul_le_mul_of_nonneg_left h₂ (sq_nonneg Q₀), mul_pos hj.outE (show 0<r from he.shoot)]
      have hX : (Q₀*φ)^2 ≤ ψ^2:= le_of_mul_le_mul_right (a:=κ) (by change W*(φ^2*(ε*r)) ≤ H at h1; linarith only [mul_le_mul_of_nonneg_right hh2 (sq_nonneg φ),h1,hW]) hκ
      nlinarith only [hy,hX,mul_pos hF hv]
   have hb : coverL L Dout ε x φ ≤ Dout*H:= by change Dout*W*M ≤_; nlinarith only [mul_le_mul_of_nonneg_left h1 hj.stampD.le]
   have ha :0≤Dout* H:= (mul_pos hj.stampD hH).le
   refine advanced L _ hD.purse hb (le_trans ?_ (b:= ψ*(Dout*H)) (le_of_eq (by rw [← mul_assoc])))
   unfold coverH; exact (mul_le_mul_of_nonneg_left hb (mul_pos hF hv).le).trans (mul_le_mul_of_nonneg_right hxV ha)
end Quant
end YM.QCD.Conductor

#print axioms YM.QCD.Conductor.Quant.stepY
#print axioms YM.QCD.Conductor.Quant.leavesY
