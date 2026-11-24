import YM.Affina.Rem
import YM.Tinus.WoodR
import YM.Tinus.Nim
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
open MassiveQCD.Sample YM.Intag YM.Intag.Receipt Basal Sail
open Rails.Bank.Hike
set_option quotPrecheck false
variable (L:Side)
local notation "W" x:arg=> (highR L x+1:ℕ)
local notation "Q" x:arg=> (↑(highR L x+1:ℕ):ℝ)
local notation "n1" x:arg=>riseV L x (W x)
local notation "B" x:arg=>highR L (n1 x)
local notation "v" x:arg=> fan L θ (n1 x)
variable (Wχ:ℕ→ℝ)(U S:ℝ)
local notation "G" x:arg=> Wχ (B x)* (v x)^2
include θ
lemma rateG (h:Rates.Fuel Wχ): Rate su L 0 (fun x=> G x):=by
   obtain ⟨K,n,hp,hK⟩:= h.gains; have hB: Rate su L 0 (fun x=> Wχ (B x)):=by
       refine (Rate.weaken ((((opusR L).mul_left 8).pow n).mul_left K) (by simp)).compare ?_
       filter_upwards [heightR L] with x hx; exact (hK (B x)).trans (((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ((hx _ le_rfl).2) n) hp)).trans (le_abs_self _))
   have hR:Rate su L 0 (fun x=> v x):= roseR L (Rate.rpow_monitor θ) (fun i=> W i) (Eventually.of_forall fun i=> le_rfl)
   exact Rate.weaken (hB.mul (hR.pow 2)) (by norm_num)
local notation "Sx" x:arg=> motor (G x) S
local notation "Zu" x:arg=> U*Sx x/(v x)^2
local notation "Ze" k:arg x:arg=>1/(Q x)^k
lemma goodness (hp:Rates.Fuel Wχ)(hθ:0<θ):∃ k:ℕ, k≥2∧ Tendsto (fun x=> Q x* (Ze k x)  * (Zu x)) atTop (𝓝 0):=by
     obtain ⟨K,n,hK,hW⟩:= hp.gains; let C:= |U| *|S|^10; let h:=(8:ℝ)^n; have hC:0 ≤C:=by unfold C; positivity
     have hu:Tendsto (fun x=> v x) atTop atTop:= ( (tendsto_rpow_atTop hθ).comp (Jets.Touch.Seat.your L)).comp (tendsto_atTop.2 (fun _=> by apply (aheadΩ L _ (eventually_ge_atTop _)).mono; intro i hi; exact hi _)) -- namespace
     refine ⟨n+2,by omega,?_⟩; rw [Metric.tendsto_nhds]; intro ε he; let K':=(K*h+1)*C; have ht:= (tendsto_inv_atTop_zero.comp (opusT L)).mul_const K'; rw [zero_mul] at ht; filter_upwards [hu.eventually_ge_atTop 1,heightR L,ht.eventually_le_const (show 0 < ε/2 from by positivity)] with x hx hp hv
     let m:= Q x; have hm:1 ≤ m:=by unfold m; simp
     let r:= v x; have hr:1 ≤ r:=hx; have hb:0 < m:=zero_lt_one.trans_le hm; have hg:1 ≤ r^2:=one_le_pow₀ hr; let c:= Wχ (B x); have hc:|c| ≤ K*(8*m)^n:=(hW _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ((hp _ le_rfl).2) _) hK)
     have hd:(|c*r^2|+1)/(r^2) ≤ (K*h+1)*m^n:=by rw [abs_mul,abs_of_nonneg (sq_nonneg r),add_div]; rw [mul_div_cancel_right₀ |c| (zero_lt_one.trans_le hg).ne']; apply (add_le_add hc ((div_le_iff₀ (zero_lt_one.trans_le hg)).2 (show 1≤1*r^2 from (one_mul (r^2)).symm ▸ hg))).trans; rw [mul_pow]; unfold h; nlinarith only [one_le_pow₀ hm (n:=n)]
     have hD:|Zu x|≤ K'*m^n:=by
         rw[abs_div,abs_mul]; unfold Receipt.motor; change |U| * |(|c*r^2|+1)*S^10|/|r^2|≤ _; rw[abs_mul, abs_of_nonneg (add_nonneg (abs_nonneg (c*r^2)) zero_le_one), abs_pow,abs_of_nonneg (sq_nonneg r)]; unfold K'
         refine le_trans (b:= C*((|c*r^2|+1)/r^2)) ?_ ?_
         · unfold C; exact le_of_eq (by ring)
         exact ((mul_le_mul_of_nonneg_left hd hC)).trans_eq (by ring)
     rw [Real.dist_eq,sub_zero,abs_mul]; let A:= m*(1/m^(n+2)); have hA:0≤A:= mul_nonneg hb.le (div_nonneg zero_le_one (pow_nonneg hb.le _)); change |A| *|Zu x|< ε; rw [abs_of_nonneg hA]; refine ((mul_le_mul_of_nonneg_left hD hA).trans_eq (show A*(K'*m^n)=m⁻¹*K' from by unfold A; rw [pow_add]; field_simp)).trans_lt (lt_of_le_of_lt hv (show ε/2<ε from by linarith))
omit θ
lemma notable (E:ℕ)(hE:2 ≤ E): Tendsto (fun x=> Q x *(Ze E x)) atTop (𝓝 0):=by
     refine squeeze_zero (fun x=>by positivity [show 0<Q x from Nat.cast_pos.mpr (by omega)]) (fun i=>?_ ) (tendsto_inv_atTop_zero.comp (opusT L)); let t:=Q i; have h:1 ≤ t:= by unfold t; simp
     have hh:0<t:=zero_lt_one.trans_le h; change t*(1/t^E) ≤ t⁻¹; rw [← mul_div_assoc]; apply (div_le_iff₀ (pow_pos hh _)).2; rw [mul_one]; apply le_trans (Eq.le (_: t=t⁻¹*t^2))
     · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h hE) (inv_nonneg.mpr hh.le)
     · field_simp
lemma acquire (k:ℕ) : ∀ᶠ x:ℝ in atTop,∀ j, Ivy.crawl L k (run L (riseV L x j))∈Set.Icc 0 1 ∧ Ivy.crawl L k (run L (riseV L x j)) ≤ 1/(Q x)^k:=by
       have he:0 ≤ su.slopeConstant*Real.log (L.val:ℝ):=Work.E04.shift_nonneg su L; filter_upwards [(Work.E09.betaF_growth su L).eventually_ge_atTop 1] with x hx j
       let y:=run L (riseV L x j); let t:= run L x; have hh:x ≤ y:=by
            apply le_trans (b:=riseV L x j) (le_add_of_nonneg_right (mul_nonneg (by positivity:(0:ℝ)≤↑j) he)); exact le_add_of_nonneg_right he
       have hB:t ≤ run L y:= add_le_add_left hh _; have hp:1 ≤t:=hx
       unfold Ivy.crawl; refine ⟨⟨by positivity, ?_⟩,?_⟩; exact one_div_le_one_div_of_le (by norm_num: (0:ℝ)<1) (one_le_pow₀ (le_add_of_nonneg_right (by positivity))) |>.trans_eq (one_div_one)
       have hQ : highR L x ≤ highR L y:=Nat.ceil_le_ceil (pow_le_pow_left₀ (Real.log_nonneg hp) (Real.log_le_log (zero_lt_one.trans_le hp) hB) _); exact one_div_le_one_div_of_le (pow_pos (Nat.cast_pos.mpr (by omega)) _) (pow_le_pow_left₀ (Nat.cast_nonneg _) (by rw[Nat.cast_add,Nat.cast_one,add_comm]; exact add_le_add_right (Nat.cast_le.mpr hQ) _) _)
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.acquire
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.goodness
