import YM.Talis.Spen
import YM.Magi.Rich
import YM.Bloom.Shrimp
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
open YM.Bloom.TreeP YM.Arise QCD.Bloom.Buzz QCD.Bank
variable (ν a δ H D:ℕ)
open Vest QCD.Bera Next.Rank.Normal
local notation "w"=> EV ν
local notation "W!"=> WTop L ν H
local notation "Ω"=> cutOffV L
local notation "Φ"=> freshS L 5
local notation "U!"=> (ν+1)
-- same Curtain Lens estimates appeal.Canon.E.Short.Clock.Act
variable (K bℓ l k m:ℕ) (C C' Δ' S₀:ℝ)
local notation "η"=> fun x=> freshS L 5 x
structure Chair (z y x f:ℝ)(μ Z:ℝ) : Prop where
    cG: z*(crop su (WTop L ν H x) C (BetaLeak L ν x) μ D (K*(highR L f))*y) ≤ Z
    cE: pocketV (WTop L ν H x) C' (BetaLeak L ν x) μ D (K*(highR L f)) ≤ Z
    dG: C/measureV L ν x+C*μ^2 ≤ Z
    dE: C'/measureV L ν x+C'*μ^2 ≤ Z
variable {q v ωs:ℕ}
local notation "𝔐"=> EV a
local notation "h6"=>EV 6
local notation "ZD"=> EV q
local notation "ZP"=> EV v
local notation "Yc"=> EV ωs
local notation "VK"=>Chair L ν H D K C C'
lemma gammaLeak (C:ℝ) :∀ᶠ x in atTop, C*cutOffV L (1/8) x≤(measureV L 6 x)⁻¹:=by
     filter_upwards [((Rate.power (G:=su) (L:=L) (a:=-(1/8:ℝ))).mul_left C |>.mul (rateMeasure L 6)).below (by norm_num) 1 zero_lt_one] with x hx; rw[inv_eq_one_div]; apply (le_div_iff₀ (χone ..)).mpr; exact (le_abs_self _).trans hx
-- uniform bills, post setup slots. Use scream.M.TypeB primary EPA.
lemma lampA (hL:1<L.val)(hq:q<a)(hv:q<ν)(hw:ωs<q)(ht:6 ≤ωs)(hp:0≤ C)(hp':0≤ C') : ∀ᶠ x in atTop,(∀ i≤distV L U! x,VK (2*gemmaV L x) (freshS L 5 x) x (riseV L x i) (measureV L a x)⁻¹ (measureV L q x)⁻¹) ∧ (cutOffV L (1/8) x+(EV ωs x)^l*(Arise.Count.corona (Δ'+(EV q x)⁻¹) S₀ k m l*(EV q x)⁻¹) ≤ (EV 6 x)⁻¹) ∧ ∀ i≤distV L U! x,(fan L θ (riseV L x i))^(l*m)*(EV ωs x)^l*S₀ ≤ run L (riseV L x i):=by -- S₀ maybe need ≥0
     have hZ:PageP L (fun x=> Arise.Count.corona (Δ'+(EV q x)⁻¹) S₀ k m l) ωs:= ((PageP.just L Δ' _).harm L (PageP.seed ..)).fBanner L k m l S₀; have hp:=hp
     have hT:PageP L (fun x=> EV 6 x * ((EV ωs x)^l*Arise.Count.corona (Δ'+(EV q x)⁻¹) S₀ k m l)) ωs := (PageP.budget_lo L ht).times L (((PageP.loan L _).liftNat L l).times L hZ)
     have hr:Rate su L 0 (fun x=> (EV 3 x)^(l*m)*(EV ωs x)^l*|S₀|):=by
           refine Rate.weaken (Rate.mul_right (Rate.mul ((rateMeasure L 3).pow _) ((rateMeasure L ωs).pow _)) _) (by norm_num)
     filter_upwards [ofSeat L hL (support_x L) (ν+1),arcsA L ν a H D K C C' hL hq hv (by omega),curtailV L (ν+1) θ hL,lapsV L (ν+1), hr 1 zero_lt_one,hT.absorb L hL hw (1/2) (by norm_num),gammaLeak L 2,Delay.shift_pos su L] with x hx hv hy he hC ht h hp0; let Z:=(EV q x)⁻¹; let G':=2*gemmaV L x;  let Y:=(EV a x)⁻¹; have hG: 0<G':= mul_pos (by norm_num) (mul_pos (by norm_num) (Real.rpow_pos_of_pos hp0 _))
     have he0 :0< measureV L ν x:=χone ..; have hX:0< h6 x:=χone ..; have hf:0 < freshS L 5 x:= mul_pos (lightsV L x hp0 (1/2)) (χone ..); obtain ⟨h₁,h₂,h₃,h₄⟩:=hv
     refine ⟨fun i hi=>?_,?_,fun i hi=>?_⟩
     · let B:= highR L (riseV L x i); have hV:B ≤ topC L x:=by apply Nat.cast_le (α:=ℝ)|>.mp; exact (le_abs_self _).trans ((hx i hi).trans (Nat.le_ceil _))
       have hk: K*B ≤ K*topC L x:=Nat.mul_le_mul_left _ hV; have hp'':0≤ BetaLeak L ν x:=(mul_pos (lightsV L x hp0 1) (χone ..)).le; have hM:0≤Y:=(inv_pos.mpr (χone ..)).le; have hG0:0 ≤ WTop L ν H x:=zero_le_one.trans (joy ν H x)
       refine ⟨?_,(cuffR D hp' hp'' hM hG0 hk).trans h₂,h₃,h₄⟩
       rw [mul_comm _ (freshS L 5 x),←mul_assoc]; exact (mul_le_mul_of_nonneg_left (chopR D hp hp'' hM hG0 hk) (mul_pos hG hf).le).trans h₁ -- maybe comm wrong
     · let p:=(EV ωs x)^l; let W:= Arise.Count.corona (Δ'+ Z) S₀ k m l
       have ht' : p*(W*Z) ≤ (1/2)/h6 x:= (le_div_iff₀ hX).mpr (le_trans (le_of_eq (show p*(W*Z) * EV 6 x = EV 6 x*(p*W)/EV q x from by unfold Z; ring)) ht)
       change cutOffV _ _ x+ p*(W*Z) ≤ _; rw [div_eq_mul_inv (1/2:ℝ)] at ht'; linarith only [h,ht']
     · simp only [Real.rpow_one] at hC; let s:=fan L θ (riseV L x i); have hv:0<s:=fan_pos ..; have hw:0≤ EV ωs x:=χone ..|>.le
       refine le_trans (mul_le_mul_of_nonneg_left (le_abs_self S₀) (mul_nonneg (pow_nonneg hv.le _) (pow_nonneg hw _))) ?_; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.le (hy i hi) _) (pow_nonneg hw _)) (abs_nonneg _)).trans (((le_abs_self _).trans hC).trans (he i hi).1)
lemma lampB (hL:1<L.val)(hw:v<ωs)(ht:6 ≤ v)(hp:0≤ C)(hp':0≤ C') (Y:ℝ)(he:Y≥0)(hc:1≤ Δ')(hX:1≤ S₀)(hq:q<v)(hd:5≤ q): ∀ᶠ x in atTop,(∀ i≤distV L U! x,VK (2*gemmaV L x) (freshS L 5 x) x (riseV L x i) (measureV L q x) (measureV L v x)) ∧ (cutOffV L (1/8) x+(EV ωs x)⁻¹*(Arise.Count.corona (Δ'+EV v x) S₀ k m l*(EV v x)+Y) ≤ (EV 6 x)⁻¹):=by
     have hZ : PageP L (fun x=> Arise.Count.corona (Δ'+EV v x) S₀ k m l) v:= ((PageP.just L Δ' _).harm L (PageP.loan ..)).fBanner L k m l S₀
     have hT:PageP L (fun x=> EV 6 x*(Arise.Count.corona (Δ'+EV v x) S₀ k m l*(EV v x)+Y)) v := (PageP.budget_lo L ht).times L ((hZ.times L (PageP.loan ..)).harm L (PageP.just L Y _))
     filter_upwards [ofSeat L hL (support_x L) (ν+1),arcsB L ν H D K C C' hL hd hq,hT.absorb L hL hw (1/2) (by norm_num),gammaLeak L 2,Delay.shift_pos su L] with x hx hv ht h hp0; let G':=2*gemmaV L x;  let M:=EV q x; have hG: 0<G':= mul_pos (by norm_num) (mul_pos (by norm_num) (Real.rpow_pos_of_pos hp0 _))
     have hX:0< h6 x:=χone ..; have hf:0 < freshS L 5 x:= mul_pos (lightsV L x hp0 (1/2)) (χone ..); obtain ⟨h₁,h₂,h₃,h₄⟩:=hv; refine ⟨fun i hi=>?_,?_⟩
     · let B:= highR L (riseV L x i); have hV:B ≤ topC L x:=by apply Nat.cast_le (α:=ℝ)|>.mp; exact (le_abs_self _).trans ((hx i hi).trans (Nat.le_ceil _))
       have hk: K*B ≤ K*topC L x:=Nat.mul_le_mul_left _ hV; have hp'':0≤ BetaLeak L ν x:=(mul_pos (lightsV L x hp0 1) (χone ..)).le; have hM:0≤ M:=χone L x q|>.le; have hG0:0 ≤ WTop L ν H x:=zero_le_one.trans (joy ν H x)
       refine ⟨?_,(cuffR D hp' hp'' hM hG0 hk).trans h₂,h₃,h₄⟩
       rw [mul_comm _ (freshS L 5 x),←mul_assoc]; exact (mul_le_mul_of_nonneg_left (chopR D hp hp'' hM hG0 hk) (mul_pos hG hf).le).trans h₁
     · let V:=Arise.Count.corona (Δ'+EV v x) S₀ k m l*(EV v x)+Y; have ht' : (EV ωs x)⁻¹ * V ≤ (1/2)/h6 x:= (le_div_iff₀ hX).mpr (le_trans (by apply le_of_eq; exact show ((EV ωs x)⁻¹* V)* EV 6 x= EV 6 x*V/EV ωs x from by ring) ht)
       change cutOffV _ _ _+ (EV ωs x)⁻¹ * V ≤ _; rw [div_eq_mul_inv (1/2:ℝ)] at ht'; linarith only [h,ht']
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.lampB
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.lampA
