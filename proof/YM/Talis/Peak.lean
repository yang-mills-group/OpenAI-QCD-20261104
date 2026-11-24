import YM.Bard.Kite
import YM.Bard.Reel
import YM.Magi.Band
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
variable {S:Flight j j}{K:KernelChoices}{hBP:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K hBP)}
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
namespace Talis
open MintV Suburb.Affair.Nimbus Counter
variable (L:Side)
local notation "EV"=> measureV L
local notation "τ"=>distV L
local notation "Bp"=>run L
-- costs closed under polynomials at fixed lens apertures; scheduling.S ANY incl 0.
structure PageP (P:ℝ→ℝ)(a:ℕ) :Prop where
    rent : ∃ (C:ℝ)(k:ℕ),0≤ C ∧∀ᶠ x in atTop,|P x| ≤ C*(measureV L a x)^k
namespace PageP
variable {K R:ℝ→ℝ}{A B:ℕ}(h:PageP L K A)(hR:PageP L R A)
lemma just (C:ℝ) (a:ℕ): PageP L (fun _=>C) a:=⟨|C|,0,abs_nonneg _,Eventually.of_forall fun x=>by simp⟩
lemma loan (a:ℕ):PageP L (measureV L a) a:=⟨1,1,zero_le_one,Eventually.of_forall fun i=> by rw[pow_one,one_mul,abs_of_nonneg (χone L i a|>.le)]⟩
include h
lemma takes (hx: ∀ᶠ v in atTop, |R v|≤ |K v|): PageP L R A:=by obtain ⟨C,k,hC,h⟩:=h.rent; exact ⟨C,k,hC,(hx.and h).mono fun x h=>h.1.trans h.2⟩
lemma thin (hx: ∀ᶠ v in atTop,K v=R v): PageP L R A:=h.takes L (hx.mono fun x h=> by rw[h])
lemma out (hA:A ≤ B): PageP L K B:=by
    obtain ⟨C,k,hC,h⟩:= h.rent; refine ⟨C,k,hC,?_⟩; filter_upwards [h,(buysV L).eventually_ge_atTop 1] with x hx hV using hx.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (χone L x A|>.le) (outR L _ _ x hV hA) k) hC)
include hR
lemma times : PageP L (fun x=> K x*R x) A:=by
   obtain ⟨C,k,hC,h⟩:=h.rent; obtain ⟨D,j,hV,hR⟩:=hR.rent; refine ⟨C*D,k+j,mul_nonneg hC hV,?_⟩; filter_upwards [h,hR] with x hx hv; rw [abs_mul,pow_add]; exact (mul_le_mul hx hv (abs_nonneg _) ((abs_nonneg ..).trans hx)).trans (by apply le_of_eq; ring)
lemma harm : PageP L (fun x=> K x+R x) A:=by
   obtain ⟨C,k,hC,h⟩:=h.rent; obtain ⟨D,j,hV,hR⟩:=hR.rent; refine ⟨C+D,k+j,add_nonneg hC hV,?_⟩; filter_upwards [h,hR] with x hx hv; rw [add_mul]; apply le_trans (abs_add_le ..); exact add_le_add (hx.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (uniformV ..) (by omega)) hC)) (hv.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (uniformV ..) (by omega)) hV))
lemma top : PageP L (fun x=> max (K x) (R x)) A:=by
   obtain ⟨C,k,hC,h⟩:=h.rent; obtain ⟨D,j,hV,hR⟩:=hR.rent; refine ⟨max C D,max k j,hC.trans (le_max_left ..),?_⟩; filter_upwards [h,hR] with x hx hv; rcases le_total (K x) (R x) with hh|hh
   · rw[max_eq_right hh]; exact hv.trans (mul_le_mul (le_max_right ..) (pow_le_pow_right₀ (uniformV ..) (le_max_right ..)) (pow_nonneg (χone L x A|>.le) _) (hC.trans (le_max_left ..)))
   rw[max_eq_left hh]; exact hx.trans (mul_le_mul (le_max_left ..) (pow_le_pow_right₀ (uniformV ..) (le_max_left ..)) (pow_nonneg (χone L x A|>.le) _) (hV.trans (le_max_right ..)))
omit hR
lemma liftNat (k:ℕ) : PageP L (fun x=> (K x)^k) A :=by induction k with|zero=>simpa only [pow_zero] using just L 1 A|succ k ih=> exact (by simp_rw [pow_succ]; exact ih.times L h)
lemma timesL (C:ℝ): PageP L (fun x=> C*K x) A:= times L (just L C A) h
lemma rate : Rate su L 0 K:=by
   have hp:=h; obtain ⟨C,k,hC,h⟩:=h.rent; intro a ha; have he:=rateMeasure L (A+1)
   rcases eq_or_lt_of_le (show 1 ≤ L.val from L.pos) with hX|hV
   · filter_upwards [h,(Rate.const (G:=su) (L:=L) C a ha)] with x hx hp; rw [abs_of_nonneg hC] at hp; simp [measureV,← hX] at hx; exact hx.trans hp
   filter_upwards [h, goCost L A (A+1) k C hV (by omega),he a ha] with x hx hV hp; rw [abs_of_nonneg (χone ..|>.le)] at hp; exact hx.trans (hV.trans hp)
lemma cheaper (hL:1<L.val)(ha:A<B):∀ᶠ x in atTop,K x ≤ EV B x:=by
    obtain ⟨C,k,hC,h⟩:=h.rent; filter_upwards [h,goCost L A B k C hL ha] with i hi hh using (le_abs_self _).trans (hi.trans hh)
lemma absorb (hL:1<L.val)(ha:A<B)(t:ℝ)(ht:0<t):∀ᶠ x in atTop,K x / (EV B x) ≤t:=by filter_upwards [(h.timesL L t⁻¹).cheaper L hL ha] with x hx; rw [inv_mul_eq_div] at hx; exact (div_le_iff₀ (χone ..)).mpr (((div_le_iff₀ ht).mp hx).trans_eq (mul_comm ..))
lemma fade (hx:0≤ a)(hq:∀ᶠ x in atTop, 0 ≤ K x) : PageP L (fun x=> (K x)^a) A:=by
      refine ((h.liftNat L ⌈a⌉₊).top L (just L 1 _)).takes L ?_; filter_upwards [hq] with x hx'; change |(K x)^a|≤ |max ((K x)^⌈a⌉₊) 1|; rw [abs_of_nonneg (Real.rpow_nonneg hx' _)]; apply le_trans _ (le_abs_self _); rcases le_total 1 (K x) with hh |hh; · apply le_trans _ (le_max_left ..); simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hh (Nat.le_ceil a)
      exact (Real.rpow_le_one hx' hh hx).trans (le_max_right ..)
omit h
lemma budget_lo (ha:A ≤ B): PageP L (EV A) B:=(loan L A).out L ha
lemma seed (t:ℕ) : PageP L (fun x=> (EV A x)⁻¹) t:=by apply (just L 1 _).takes; exact Eventually.of_forall fun x=>by simp only [abs_one,abs_of_nonneg (inv_nonneg.mpr (χone ..|>.le))]; exact inv_le_one_of_one_le₀ (uniformV ..)
lemma hush {v:ℝ→ℝ}(hx:Rate su L a v)(ht:a<0) : PageP L v 0:=by refine (just L 1 0).takes L ?_; simpa only [abs_one] using hx.below ht 1 zero_lt_one
-- monitor conversion
lemma seat {C:ℝ→ℝ} (hL:1<L.val)(hp:Seat L a C) : PageP L C 3:=by refine (loan L _).takes L ?_; filter_upwards [hp (a+1) (lt_add_one _),curtailV L 1 (a+1) hL] with x hx ht; have h := ht 0 (Nat.zero_le _); rw [show riseV L x 0=x from by simp[riseV]] at h; exact hx.trans (h.trans (le_abs_self _))
end PageP
-- budget comparison inverse for ratioCost and budgetV uniform
open Suburb.Melt.Lobby
lemma support_x : Seat L 0 (fun x=> (highR L x:ℝ)):=by
       intro b hb; filter_upwards [Delay.monitor_pays su L 1 (D:=1) zero_le_one hb] with x hx; refine le_trans ?_ hx; unfold highR radiusB Delay.bill; rw [abs_of_nonneg (by positivity),one_mul,pow_one]; have h := Nat.ceil_lt_add_one (sq_nonneg (Real.log (betaF su x L))); linarith only [h,Nat.cast_nonneg (α:=ℝ) (Nat.ceil (Real.log x ^2))]
lemma ofSeat (hL:1<L.val){C:ℝ→ℝ}(hp:Seat L a C)(n:ℕ):∀ᶠ x in atTop,∀ i≤ τ n x,|C (riseV L x i)| ≤ EV 3 x:=by
       filter_upwards [aheadΩ L _ (hp (a+1) (lt_add_one _)),curtailV L n (a+1) hL] with x hx ht i hi using (hx i).trans (ht i hi)
lemma capR (n:ℕ)(hL:1<L.val):∀ᶠ x in atTop,∀ i<τ n x,let y:=riseV L x i; (EV 3 x)⁻¹ ≤ ratioCostV L y ∧ ratioCostV L y ≤1:=by
      filter_upwards [curtailV L n 4 hL,aheadΩ L _ ((Seat.your L).eventually_ge_atTop 1)] with x hx hv i hi; intro y; let k:=run L y; let z:=EV 3 x; have he: k=riseV L x (i+1):=by unfold k; rw [slideV, agingV] -- check
      have hp:= fan_pos L 4 k; have h:ratioCostV L y=(fan L 4 k)⁻¹:= Real.rpow_neg (Delay.monitor_pos ..).le _ -- argument?
      rw [h]; refine ⟨inv_anti₀ hp (by unfold k y; change _ ≤_; rw[show run L (riseV L x i)= _ from he]; exact hx _ hi), inv_le_one_of_one_le₀ (Real.one_le_rpow (?_) (by norm_num))⟩; rw [he]; exact hv _
lemma capP (n:ℕ)(hL:1<L.val):∀ᶠ x in atTop,∀ i≤τ n x,let y:=riseV L x i; (EV 3 x)⁻¹ ≤2*budgetV L y ∧ 0<budgetV L y∧ budgetV L y ≤1:=by
   filter_upwards [curtailV L n 2 hL, aheadΩ L _ ((Seat.your L).eventually_ge_atTop 1)] with x hx ht i hi; intro y; let p:= fan L 2 y; have hp: 1 ≤ p:= Real.one_le_rpow (ht _) (by norm_num); have hz:0<p:= zero_lt_one.trans_le hp; have h:budgetV L y=p⁻¹/2:=by change fan L (-2) y/2=_; rw[fan,Real.rpow_neg (Delay.monitor_pos ..).le]; -- may need rfl
   rw[h]; have hv:=inv_anti₀ hz (hx _ hi); have he:=inv_le_one_of_one_le₀ hp; refine ⟨?_,by positivity,by linarith⟩; linarith only [hv]
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.capR
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.PageP.fade
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.PageP.rate
