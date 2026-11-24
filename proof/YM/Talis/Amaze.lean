import YM.Talis.Ports
import YM.TIPS.Yawn
import YM.Profiles.Counts
import YM.Talis.Billet
import YM.Talis.Ports
import YM.TIPS.Yawn
import YM.Profiles.Counts
import YM.Talis.Massy
import YM.Talis.Peak
import YM.Differ.Humming
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
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
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
open YM.Bloom.TreeP Vest QCD.Bera
open Massive.Evo Suburb.Affair.Nimbus Next.Rank
namespace Blessing
local notation "vλ"=>fan L θ
open Counter.Hymn MassiveQCD.Sample.Sail MassiveQCD.Plate Suburb.Melt.Lobby Suburb.Melt.Lobby.LifeT
-- dollarX: damping within actual SP intervals via Hᵗʸ.
variable (n a ν z d B D H:ℕ)(C C':ℝ)
local notation "ZG"=>EV ν
local notation "W!"=> WTop L ν H
noncomputable def unitK (x:ℝ):ℝ:=((L.val:ℝ)^(bookB L ν H z x))^(-Counter.Hymn.pitchD d)
local notation "G!"=>unitK L ν z d H
lemma unit_pos (x:ℝ):0<G! x:= Real.rpow_pos_of_pos (pow_pos (show (0:ℝ) < L.val from by positivity) _) _
lemma rebateV (h:FloorB L ν H B z a x): WTop L ν H x^d* unitK L ν z d H x = (EV z x)^(Counter.Hymn.pitchD d) /Real.sqrt (WTop L ν H x):=by
    unfold unitK; let Q:= Counter.Hymn.pitchD d; let p:=WTop L ν H x; let e:=EV z x; have hp:0<p:=zero_lt_one.trans_le (joy ..); have he:0< e:= χone ..; rw [prunes L ν z H x h.stop.le]; change p^d * (p^2/e)^(-Q) = _; rw[Real.rpow_neg (show 0≤ p^2/e from by positivity),Real.div_rpow (sq_nonneg p) he.le]
    have hx : (p^2)^Q=p^d*Real.sqrt p:=by
          rw [Real.sqrt_eq_rpow, ←Real.rpow_natCast p 2,←Real.rpow_natCast p d,←Real.rpow_mul hp.le,←Real.rpow_add hp]; congr 1; unfold Q Counter.Hymn.pitchD; push_cast; ring
    change _=e^Q/Real.sqrt p; rw [hx]; field_simp -- maybe ring
lemma slows {q:ℕ}(W:ℝ→ℝ)(hp:PageP L W q)(hq:q<ν)(hq₁ : z≤q)(hL:1<L.val)(ht:0<H)(g:ℝ)(hg:0<g):∀ᶠ x in atTop, W x * (measureV L z x)^ (Counter.Hymn.pitchD d) / Real.sqrt (WTop L ν H x)≤ g:=by
    let D:= Counter.Hymn.pitchD d; let K:=fun x=> W x * (EV z x)^D; have ha :PageP L K q:=by apply PageP.times L hp; exact (PageP.budget_lo L hq₁).fade L (show 0 ≤ D by unfold D Counter.Hymn.pitchD; positivity) (Eventually.of_forall fun i=> χone ..|>.le)
    filter_upwards [(ha.liftNat L 2).absorb L hL hq (g^2) (by positivity)] with x hx; let r:=Real.sqrt (WTop L ν H x); have ht' :EV ν x ≤ WTop L ν H x:=(pow_one _).symm.le.trans (pow_le_pow_right₀ (uniformV ..) (show 1 ≤ H from ht)); have hV:0 < EV ν x:=χone ..; have hQ:0<WTop L ν H x:= hV.trans_le ht'; have hy:= (div_le_iff₀ hV).mp hx
    have hW :(K x)^2 ≤g^2 * (WTop L ν H x):=(by exact hy.trans (mul_le_mul_of_nonneg_left ht' (sq_nonneg _)))
    refine (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr ?_; change K x ≤ g*r
    rw [← show r^2= WTop L ν H x from Real.sq_sqrt hQ.le,←mul_pow] at hW; nlinarith only [hW, mul_pos hg (show r>0 from Real.sqrt_pos.mpr hQ)]
-- genuine renewal possible, accepts any post C pre α.WV S costs from Tone travel. Choose Xc target value restoration EP weights at all.
local notation "Yλ"=>EV a
local notation "TG"=> tenorP L D D
local notation "χλ"=>roomAt L θ
lemma renE (f₁:ℕ)(hL:1<L.val)(ha:4≤ a)(ht:z≤ a)(hu:a<ν)(hp:0<H)(he:1 ≤ C)(hxC:1 ≤ C'):∀ᶠ x in atTop,∀ i :ℕ,i ≤ distV L (ν+1) x→
   ∀ p:ℕ, p≤d →∀ t:ℝ,0 ≤ t→ t ≤ (WTop L ν H x)^p*tenorP L D D x→∀ e δ:ℕ,FloorB L ν H δ z e x→let y:=riseV L x i; let s':=roomAt L θ y; let b':=highR L y; let k:=measureV L a x*t*unitK L ν z d H x*C / s'; let P:= max 1 k; taxK L y (7/8)*P ≤taxK L y 1 ∧ 2*P≤Real.exp ((1/32:ℝ)/64*b')∧ s'+ P*(MassiveQCD.Plate.Stags.bonus f₁ b' (1/32)*(C'*s')) ≤ budgetV L y:=by
    -- eB reserved. choose ancillary Q≪ via lemma slows. upperBeta polynomial. bound independent of s_
    let Z:=measureV L 3; let R:=WTop L ν H; let U:=unitK L ν z d H; let D':=tenorP L D D; let A:=EV a
    let Q:=fun x=> (8:ℝ)*Z x* (Z x*C')*(A x*D' x*C)
    have heP:PageP L Z a:=PageP.budget_lo L (by omega)
    have hQ:PageP L Q a:= ((heP.timesL L 8).times L (heP.times L (PageP.just L C' a))).times L (((PageP.loan L a).times L (berth L D D |>.out L ha)).times L (PageP.just L C a))
    have hg:= slows L ν z d H Q hQ hu ht hL hp 1 zero_lt_one -- order likely no a
    let G:= fun y:ℝ=>1+ (roomAt L θ y)⁻¹
    have hz:Rate su L 1 G:=(Rate.weaken (Rate.const 1) zero_le_one).add (inverseSlot L θ)
    let v:= -((1/32:ℝ)/64); have hM: Rate su L (-3) (fun x=> Real.exp (v*highR L x)):=by unfold v; exact QCD.Hearth.paysA (ε:=1/32/64) (-3) (by norm_num) L -- check
    have hT:= (Rate.mul (hz.mul_left 2) hM).below (by norm_num) 1 zero_lt_one
    have hX:∀ᶠ x in atTop,∀ i≤distV L (ν+1) x,(8:ℝ)*Z x*(1+Z x*C')*|roomAt L θ (riseV L x i)|≤1:=by
           have hx: Rate su L (-1/2) (fun x=> 8*Z x*(1+Z x*C')*(Bp x^(-(1/2):ℝ))):=by
               exact (Rate.mul (PageP.rate L ((heP.timesL L 8).times L (PageP.harm L (PageP.just L 1 _) (heP.times L (PageP.just L C' _))))) (Rate.power)).weaken (by norm_num)
           filter_upwards [atickV L _ (slotR L θ) (by norm_num:(-1:ℝ)< -(1/2)) (by norm_num) (ν+1),hx.below (by norm_num) 1 zero_lt_one] with x he h i hi
           exact (mul_le_mul_of_nonneg_left (he i hi) (by have hm:1 ≤ Z x:=uniformV ..; have hh:0<C':= lt_of_lt_of_le zero_lt_one hxC; positivity)).trans ((le_abs_self _).trans h)
    filter_upwards [hg,hX,aheadΩ L _ (upperTax L (1/8) (by norm_num) G 1 hz),aheadΩ L _ hT,aheadΩ L _ (shuttle L θ),ofSeat L hL (MassiveQCD.Sample.Sail.bumpedH L f₁ (1/32)) (ν+1),capP L (ν+1) hL] with x hx₁ hxb ht₁ ht hp hb hV i hi p hq t hs hf e δ H₀
    intro y s' b' k P
    let w:=Q x; let F:=A x*t*U x*C; have hr:0< U x:=unit_pos ..; have hr1:1 ≤ Z x:=uniformV ..; have he':0<C:=lt_of_lt_of_le zero_lt_one he; have hx':0<C':=lt_of_lt_of_le zero_lt_one hxC; have hZZ:0<Z x:= zero_lt_one.trans_le hr1
    have hτ:0<s':= (hp i).1; have hz:= pow_le_pow_right₀ (joy (L:=L) ν H x) hq; have hd':0 ≤ D' x:=by unfold D' tenorP; positivity [χone L x 3,χone L x 4]
    have hG : (8:ℝ)* Z x*(Z x*C')*F ≤1:=by
           have hF : F ≤ (A x * ((R x)^d*D' x))* U x*C:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans hf (mul_le_mul_of_nonneg_right hz hd')) (zero_le_one.trans (uniformV ..))) hr.le) he'.le
           have htV : (R x)^d*(U x)= (EV z x)^(pitchD d)/ Real.sqrt (R x) := rebateV L e ν z d δ H H₀ -- order
           have hh:=mul_le_mul_of_nonneg_left hF (show 0 ≤ (8:ℝ)*Z x*(Z x*C') by positivity)
           refine hh.trans (le_trans ?_ hx₁); apply le_of_eq; calc
                  _=Q x*((R x)^d*U x):=by unfold Q; ring
                  _= _:=by rw [htV]; ring
    have hF':0 ≤ F:=mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans (uniformV L x a)) hs) hr.le) he'.le
    have hF:F ≤1:=by
          apply le_trans _ hG; have hh:1 ≤ (8:ℝ)*Z x*(Z x*C'):=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hr1) (one_le_mul_of_one_le_of_one_le hr1 hxC); exact le_mul_of_one_le_left hF' hh
    have hP:P≤ G y:=by
         change max 1 (F/s') ≤ 1+s'⁻¹; refine max_le (le_add_of_nonneg_right (by positivity)) ?_; exact (div_le_div_of_nonneg_right hF hτ.le).trans_eq (one_div _) |>.trans (le_add_of_nonneg_left zero_le_one)
    refine ⟨?_,?_,?_⟩
    · apply (mul_le_mul_of_nonneg_left (hP.trans (ht₁ i)) (show 0≤taxK L y (7/8) from (Real.exp_pos _).le)).trans; unfold taxK; rw[←Real.exp_add]; exact le_of_eq (by unfold y; ring_nf)
    · apply le_trans (mul_le_mul_of_nonneg_left hP (by norm_num:(0:ℝ)≤2)); have ht':2*G y*Real.exp (v*b') ≤ 1:=(le_abs_self ..).trans (ht i); unfold v at ht'; rw [neg_mul,Real.exp_neg,← div_eq_mul_inv,div_le_one (Real.exp_pos _)] at ht'; exact ht'
    have hb': MassiveQCD.Plate.Stags.bonus f₁ b' (1/32) ≤ Z x:= (le_abs_self _).trans (hb i hi)
    have hy:P≤1+k:=max_le (le_add_of_nonneg_right (show 0 ≤ F/s' from div_nonneg hF' hτ.le)) (le_add_of_nonneg_left zero_le_one); have hp':0≤ P:= zero_le_one.trans (le_max_left ..)
    let g:= MassiveQCD.Plate.Stags.bonus f₁ b' (1/32)
    have heK : s'+P*(g*(C'*s')) ≤ s'+(1+k)*(Z x*(C'*s')):= by apply add_le_add_right; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb' (by positivity)) hp').trans (mul_le_mul_of_nonneg_right hy (by positivity))
    have hw : s'+(1+k)*(Z x*(C'*s'))=(1+Z x*C')*s'+Z x*C'*F:=by change s'+(1+F/s')*_=_; field_simp; all_goals ring
    rw [hw] at heK; have hu:8*Z x*(1+Z x*C')*s'≤1:= (mul_le_mul_of_nonneg_left (le_abs_self s') (by positivity)).trans (hxb _ hi)
    apply heK.trans; apply le_trans _ (by linarith only [(hV i hi).1]: (Z x)⁻¹/2≤budgetV L y)
    rw [show (Z x)⁻¹/2=1/(2*Z x) from by ring]; apply (le_div_iff₀ (by positivity)).2; linarith only [hG,hu]
end Blessing
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.Blessing.renE -- fix
