import YM.Mistral.Num
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
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
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
namespace Mistral
open Counter Counter.Economies MassiveQCD.Sample.Eole.Gain
open Finset MintV Sapphire Talis MassiveQCD.Sample MassiveQCD.Sample.Sail MassiveQCD.Sample.Kuna
namespace RiseX
variable (L:Side)
local notation "νƒ" =>(7/8:ℝ)
local notation "P" x:arg=> run L x
local notation "λ₀"=>Real.log ((L.val):ℝ)
variable (d:ℕ)(hL:1<L.val)
local notation "λᴳ"=>globe L d
local notation "G₀"=>cash L d
local notation "s!"=> riseV L
local notation "N!"=>band L
local notation "Aᵗ" y:arg=> youngF L (mux L y) y
local notation "f★"=> mux L
-- absorb log inverses uniformly. Avoid by using cave inverse ≤P^2 & log bounds.V. Fee afterL.Ex.B
structure Wave (hb:ℕ)(θ:ℝ)(x:ℝ) :Prop where
    growsT : 32 ≤ G₀ x
    lore : 0 < λᴳ x
    denseM : 2*hb*(highR L x)^2 < N! x
    nearM : ((d:ℝ)/2+1)*((2*hb*(highR L x)^2 :ℕ)*λ₀) ≤ λᴳ x -- coeff.Tℓ
    cap (i:ℕ)(hi:i ≤2*N! x+3): (roomAt L θ (s! x i))⁻¹ ≤ G₀ x ∧ (taxK L (s! x i) ((2-1)/2))⁻¹ ≤ roomAt L θ (s! x i) ∧ 0< roomAt L θ (s! x i) ∧ roomAt L θ (s! x i)≤1
    χP (i:ℕ)(hi:i ≤2*N! x+3): (Aᵗ (s! x i))⁻¹ ≤ G₀ x
    space (i:ℕ)(hi:i ≤2*N! x+3): (f★ (s! x i):ℝ) ≤ G₀ x ∧ ((sc L (s! x i):ℕ):ℝ) ≤ G₀ x
    gainS (i:ℕ)(hi:i ≤2*N! x+3): Real.exp ((run L (s! x i))^(1/2:ℝ)) ≤ G₀ x
    pad : (N! x+1:ℕ)*λ₀ ≤ (1/(20000*((d:ℝ)+10)))*((run L x)/(2*su.slopeConstant))
    rangeK(i:ℕ)(hi:i ≤2*N! x+3): (highR L (s! x i))^2 + 10000*(f★ (s! x i))+ (10000*sc L (s! x i)) ≤ L.val^(N! x)
-- proof using RichNums. direct.U effective.
variable (θ₁:ℝ)(M₁:ℕ)

lemma τle (L:Side) (θ₁:ℝ):∀ᶠ x in atTop,(taxK L x ((2-1)/2))⁻¹ ≤ roomAt L θ₁ x:=by -- hL include L mismatch
      have ht:Rate su L (-2) (fun x=>(taxK L x ((2-1)/2))⁻¹):= Touch.couplings L (by norm_num)
      filter_upwards [(ht.mul (inverseSlot L θ₁)).below (by norm_num) 1 zero_lt_one, shuttle L θ₁] with x hx hg
      exact (div_le_one hg.1).1 (by rw [div_eq_mul_inv]; exact (le_abs_self _).trans hx)
include hL
lemma δceil (ε:ℝ)(he:0 < ε): ∀ᶠ x in atTop, (N! x+1:ℕ)*λ₀ ≤ ε*(P x/(2*su.slopeConstant)):=by
      have h:0<λ₀:= Real.log_pos (by exact_mod_cast hL); have hC:=Gauge.slopeConstant_pos simple
      let c:=ε/((2*su.slopeConstant)*λ₀)
      filter_upwards [band_w L c (show 0<c from by unfold c; positivity)] with x hx; apply (mul_le_mul_of_nonneg_right hx h.le).trans_eq (by unfold c; field_simp) |>.trans le_rfl
include d
lemma rangesK :∀ᶠ x in atTop,∀ i≤2*N! x+3,(highR L (s! x i))^2 + 10000*(f★ (s! x i))+ (10000*sc L (s! x i)) ≤ L.val^(N! x):=by
      have h:0<λ₀:= Real.log_pos (by exact_mod_cast hL)
      let f (y:ℝ):ℕ:= (highR L y)^2 +10000*(f★ y)+10000*sc L y
      have hF:Rate su L 0 fun y=>(f y:ℝ):=by unfold f; push_cast; exact (((((base_rate L).pow 2).weaken (by ring_nf; try rfl)).add ((mux_rate L).mul_left _)).add ((sx_rate L).mul_left _))
      filter_upwards [(upb L).eventually_ge_atTop 1, richNums L hL d _ hF 1 zero_lt_one] with x hp hx i hi
      have hf:(f (s! x i):ℝ) ≤ λᴳ x:= ((le_abs_self _).trans (hx i hi)|>.trans_eq (one_mul _))
      refine Nat.cast_le (α:=ℝ)|>.mp (hf.trans ?_); push_cast; rw [show (↑L.val:ℝ)^ _= _ from (show (↑L.val:ℝ)^(N! x)=Real.exp (((N! x):ℝ)*λ₀) from (by rw [Real.exp_nat_mul,Real.exp_log (by positivity)]))]; have he:= Real.add_one_le_exp (((N! x):ℝ)*λ₀); apply le_trans _ he; unfold globe; push_cast; rw [div_le_iff₀ (show 0< (10000*((d:ℝ)+10)) from by positivity)]; have hw:1≤ (N! x:ℝ):=by exact_mod_cast hp; -- nlinarith
      nlinarith only [h,hw,mul_nonneg h.le (mul_nonneg (show 0≤ (N! x:ℝ) from (by positivity)) (Nat.cast_nonneg (α:=ℝ) d)), show 0≤ (d:ℝ) from (by positivity), mul_nonneg h.le (sub_nonneg.mpr hw)]
lemma acclaim : ∀ᶠ x in atTop, 1 ≤ run L x→Wave L d M₁ θ₁ x:=by
      have hl:0<λ₀:= Real.log_pos (by exact_mod_cast hL)
      let C:= (d:ℝ)/2+1; let U(v:ℝ):= ((2*M₁*(highR L v)^2:ℕ):ℝ); let U0(v:ℝ):= C*((U v)* λ₀)
      have hu:Rate su L 0 U0:=by unfold U0 U; push_cast; let e:=(M₁:ℝ); exact (((((base_rate L).pow 2).weaken (by ring_nf; try rfl)).mul_left (2*(M₁:ℝ))).mul_right _ |>.mul_left C)
      have hY:= richNums L hL d _ (logsV L (mux L) (mux_rate L)) 1 zero_lt_one
      have hs : ∀ᶠ x in atTop,∀ i≤2*N! x+3,(P (s! x i))^(2:ℝ) ≤ G₀ x:=by
          have hX: Rate su L 0 (fun y=>Real.log ((P y)^(2:ℝ))):= by
                -- use radius.Already in Cave. cost log^2 ≤ B.Fund
                apply Rate.compare ((base_rate L).mul_left 2)
                filter_upwards [(Work.E09.betaF_growth su L).eventually_ge_atTop (Real.exp 1)] with y hy; have hf:0<P y:= (Real.exp_pos _).trans_le hy
                rw [Real.log_rpow hf]; change |(2:ℝ)*Real.log (run L y)| ≤ _; have hG:= (Real.le_log_iff_exp_le hf).2 hy; exact le_trans (le_of_eq (abs_of_nonneg (mul_nonneg (by norm_num) (show 0 ≤ _ from zero_le_one.trans hG)))) ((mul_le_mul_of_nonneg_left (le_trans (show Real.log (P y) ≤ (Real.log (P y))^2 from (by nlinarith only[hG])) (Nat.le_ceil _)) (show 0 ≤ (2:ℝ) from by norm_num)).trans (le_abs_self (2*(highR L y:ℝ))))
          filter_upwards [richNums L hL d _ hX 1 zero_lt_one,aheadΩ L _ (Delay.shift_pos su L)] with x hx hp i hi
          exact (Real.log_le_log_iff (Real.rpow_pos_of_pos (hp i) _) (Real.exp_pos _)).1 (le_trans ((le_abs_self _).trans (hx i hi)) (by rw [Real.log_exp,one_mul]))
      filter_upwards [(globe_top L hL d).eventually_gt_atTop 0, (Real.tendsto_exp_atTop.comp (globe_top L hL d)).eventually_ge_atTop 32,hY,richNums L hL d _ (sx_rate L) 1 zero_lt_one, richNums L hL d _ (mux_rate L) 1 zero_lt_one,fw L hL d (1/2) 1 (by norm_num) (by norm_num) zero_lt_one, richNums L hL d _ hu 1 zero_lt_one,(upb L).eventually_ge_atTop 1,δceil L hL _ (show 0<(1/(20000*((d:ℝ)+10))) from by positivity),hs,rangesK L d hL,aheadΩ L _ (Counter.cave L θ₁),aheadΩ L _ (τle L θ₁)] with x hp hF hx hS hU hω hκ hζ hq hT hr hz hG ht -- height ordering
      have he:U0 x ≤ λᴳ x:=by have hv:= hκ 0 (show 0≤ _ from Nat.zero_le _); rw[riseV,Nat.cast_zero,zero_mul,add_zero,one_mul] at hv; exact (le_abs_self _).trans hv
      have hΔ: λᴳ x ≤ G₀ x := le_trans (by linarith only [hp]:λᴳ x ≤ λᴳ x+1) (Real.add_one_le_exp _)
      refine ⟨hF,hp,?_,he,(?_),(?_),(?_),(?_),hq,hr⟩
      · have hC:1 ≤ C:=by unfold C; have h :0 ≤ (d:ℝ):=Nat.cast_nonneg _; linarith
        unfold U0 at he; unfold globe at he; have ht0 :U x*λ₀ ≤ (λᴳ x):=le_trans (le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg _) hl.le) hC) he
        refine Nat.cast_lt (α:=ℝ)|>.mp ((mul_lt_mul_iff_left₀ hl).mp (?_)); change U x* λ₀ < (band L x:ℝ)*λ₀; apply ht0.trans_lt; unfold globe; push_cast; rw [div_lt_iff₀ (by positivity:0<(10000*((d:ℝ)+10)))]; have hw:1 ≤ (N! x:ℝ):=Nat.one_le_cast.mpr hζ; nlinarith only [hw,hl,mul_nonneg (mul_nonneg hl.le (show 0≤ (d:ℝ) from by positivity)) (show 0 ≤ (N! x:ℝ) from by positivity)]
      · intro i hi; have h:=(hz i).shape; exact ⟨h.2.2.trans (hT i hi),hG _,h.1,h.2.1⟩
      · intro i hi; let v:=Aᵗ (s! x i); have h:0 < v:=opens L ..; apply (Real.log_le_log_iff (inv_pos.mpr h) (Real.exp_pos _)).1; rw[Real.log_exp,Real.log_inv]; exact ((neg_le_abs _).trans (hx _ hi)).trans_eq (one_mul _)
      · intro i hi; exact ⟨((le_abs_self _).trans (hU i hi)).trans (((one_mul _).le).trans hΔ), ((le_abs_self _).trans (hS i hi)).trans (((one_mul _).le).trans hΔ)⟩
      · intro i hi; exact Real.exp_monotone ((hω i hi).trans_eq (one_mul _))
end RiseX
end Mistral
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Mistral.RiseX.acclaim
