import YM.Bard.Track
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
variable (L:Side)
-- floor of log log clock; movement distance pp steps.Post.L.
noncomputable def lapV (x:ℝ):= Real.log (Real.log (run L x))
noncomputable def ticksV (x:ℝ):= ⌊lapV L x⌋₊
local notation "ck"=>ticksV L
local notation "Bᵥ"=>run L
local notation "Ω"=>lapV L
noncomputable abbrev distV (n:ℕ)(x:ℝ):= ticksV L x^n
noncomputable abbrev measureV (n:ℕ)(x:ℝ):ℝ:= (L.val:ℝ)^(distV L n x)
lemma livesV : Tendsto Ω atTop atTop:= Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth su L))
lemma buysV : Tendsto ck atTop atTop:= tendsto_nat_floor_atTop.comp (livesV L)
lemma savingsV (a:ℝ)(n:ℕ)(hp:0<a):∀ᶠ x in atTop,(↑(distV L n x):ℝ) ≤ a*Real.log (Bᵥ x):=by
    filter_upwards [(livesV L).eventually_ge_atTop 0,(Real.tendsto_log_atTop.comp (Work.E09.betaF_growth su L)).eventually_gt_atTop 0,(livesV L).eventually ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).eventually_le_const hp)] with x h hp' hQ
    have ht:(Ω x)^n*Real.exp (-(Ω x)) ≤ a:=hQ
    rw [Real.exp_neg (Ω x),show Real.exp (Ω x)= Real.log (run L x) from Real.exp_log hp',← div_eq_mul_inv] at ht
    apply le_trans (b:= (Ω x)^n) _ ((div_le_iff₀ hp').mp ht); push_cast [distV]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le h) _
set_option quotPrecheck false
local notation "pL"=> (↑L.val:ℝ)
lemma uniformV (x:ℝ)(i:ℕ):1≤ measureV L i x:= one_le_pow₀ (show 1≤ pL from by exact_mod_cast L.pos)
lemma rateMeasure (i:ℕ): Rate su L 0 (measureV L i):=by
    intro a ha; let Z:=Real.log pL; have hz:Z≥0:=Real.log_nonneg (by exact_mod_cast L.pos); have hV:Z+1>0:=by linarith
    let b:= a/(Z+1); have hb:0<b:=div_pos ha hV
    filter_upwards [savingsV L b i hb,Delay.shift_pos su L] with x hx hp; have hQ:0< measureV L i x:=zero_lt_one.trans_le (uniformV ..); rw [abs_of_pos hQ]; apply (Real.log_le_log_iff hQ (Real.rpow_pos_of_pos hp _)).mp; rw [measureV,Real.log_pow,Real.log_rpow hp]; change _*Z≤_
    have hD: (↑(distV L i x):ℝ) ≤ _:=hx
    have hf : b*(Z+1)=a:=div_mul_cancel₀ _ hV.ne'
    calc _≤ (distV L i x:ℝ)*(Z+1):=mul_le_mul_of_nonneg_left (by linarith) (by positivity)
         _ ≤ (b*Real.log (Bᵥ x))*(Z+1):=mul_le_mul_of_nonneg_right hD hV.le
         _ = _ := by rw [mul_right_comm,hf]
lemma lap_pre (x:ℝ) (h:1≤ Bᵥ x)(hi:i≤k): riseV L x i ≤ riseV L x k:= (by unfold riseV; exact add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) (Work.E04.shift_nonneg su L)) x ) -- h unused
lemma lapsV (i:ℕ): ∀ᶠ x in atTop,∀ j, j≤ distV L i x →Bᵥ x ≤ Bᵥ (riseV L x j) ∧ Bᵥ (riseV L x j) ≤ 2*Bᵥ x :=by
   let u:ℝ:= su.slopeConstant * Real.log pL; have hU:0≤ u:= Work.E04.shift_nonneg su L; have hV:0<u+1:=by linarith
   filter_upwards [Delay.shift_pos su L,savingsV L (u+1)⁻¹ i (inv_pos.mpr hV)] with x hx hv j hj
   have hf:(j:ℝ) ≤ (u+1)⁻¹*Real.log (Bᵥ x):= (Nat.cast_le.mpr hj).trans hv; have ht:(j:ℝ) * (u+1) ≤ (u+1)⁻¹*Real.log (Bᵥ x) * (u+1):=mul_le_mul_of_nonneg_right hf hV.le
   rw [mul_right_comm,inv_mul_cancel₀ hV.ne',one_mul] at ht; change x+u ≤ x+j*u+u ∧ x+j*u+u≤ 2*(x+u); have he: (j:ℝ)*u ≤ (x+u):= (mul_le_mul_of_nonneg_left (by linarith: u ≤ u+1) (by positivity: (0:ℝ)≤j)).trans (ht.trans ((Real.log_le_sub_one_of_pos hx).trans (by linarith:run L x-1 ≤ run L x))); constructor <;> linarith only [he,mul_nonneg (by positivity:(0:ℝ)≤j) hU]
lemma aheadΩ (A:ℝ→Prop) (hp:∀ᶠ x in atTop,A x):∀ᶠ x in atTop,∀ j,A (riseV L x j) :=by obtain ⟨a,h⟩:= eventually_atTop.mp hp; filter_upwards [eventually_ge_atTop a] with x hx j using h _ (hx.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (Work.E04.shift_nonneg su L))))
lemma dollsV (v:ℕ):∀ᶠ x in atTop,∀ j ≤ distV L v x,ck x ≤ ck (riseV L x j) ∧ Ω (riseV L x j) ≤ 4*(ck x:ℝ):=by
    filter_upwards [(Work.E09.betaF_growth su L).eventually_gt_atTop 2,(livesV L).eventually_gt_atTop 4,(buysV L).eventually_ge_atTop 4,lapsV L v] with x hx hp he hQ j hj
    let t:= Bᵥ x; let z':=riseV L x j; obtain ⟨hv,H⟩:= hQ _ hj
    have ht:t>1:=lt_trans (by norm_num) hx; have hW:0 < Real.log t:= Real.log_pos ht; have hc :0< t:=lt_trans zero_lt_one ht
    have hu: Real.log t ≤ Real.log (Bᵥ z'):=Real.log_le_log hc hv
    refine ⟨Nat.floor_le_floor (Real.log_le_log hW hu),?_⟩
    have hm: Real.log (Bᵥ z') ≤ 2 *Real.log t:=by
        have hr:= Real.log_le_log (hc.trans_le hv) H; rw [Real.log_mul (by norm_num) hc.ne'] at hr; exact hr.trans (by change _ + _ ≤ 2*Real.log t; linarith only [Real.log_le_log (by norm_num: (0:ℝ)<2) (by exact hx.le:2 ≤ t)])
    apply (Real.log_le_log (hW.trans_le hu) hm).trans; rw [Real.log_mul (by norm_num) hW.ne']; have hΦ: Real.log (Real.log t) ≤ (ck x:ℝ)+1:=(Nat.lt_floor_add_one (Ω x)).le; linarith only [hΦ,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2), show (ck x:ℝ)≥4 from (by exact_mod_cast he)]
local notation "βx"=> Bᵥ x
lemma tonicV (hf:1<L.val)(hq:0<k): Tendsto (measureV L k) atTop atTop:= (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hf :1 < pL)).comp (by
    apply Filter.tendsto_atTop.mpr; intro x; filter_upwards [ (buysV L).eventually_ge_atTop 1,(buysV L).eventually_ge_atTop x] with i hi hh; exact hh.trans ((pow_one (ck i)).symm.le.trans (pow_le_pow_right₀ hi (show 1 ≤ k from hq))))
lemma priceL (v a b:ℕ)(h:1<L.val)(hb:a<b)(D:ℕ) : ∀ᶠ x in atTop, ∀ i≤ distV L v x, measureV L a (riseV L x i)^D ≤ measureV L b x:=by
   have hw : 1 ≤ pL:=by exact_mod_cast (show 1 ≤ L.val from h.le)
   filter_upwards [dollsV L v,(buysV L).eventually_ge_atTop (max 1 (4^a*D)),(livesV L).eventually_ge_atTop (0:ℝ), (Work.E09.betaF_growth su L).eventually_ge_atTop 2] with x hx hp hC hV i hq
   let k:=ck x; let y:=riseV L x i
   have hy: Ω y ≥ Ω x:=by
        have ht:(1:ℝ)< Bᵥ x:=lt_of_lt_of_le (by norm_num) hV; have hz:= Real.log_pos ht; have hu: x≤y:=le_add_of_nonneg_right (mul_nonneg (by positivity) (Work.E04.shift_nonneg su L)); exact Real.log_le_log hz (Real.log_le_log (by linarith) (by exact add_le_add_left hu _)) -- order
   have hm:ck y≤ 4*k:=by exact_mod_cast (show (ck y:ℝ) ≤ 4*k from ((Nat.floor_le (hC.trans hy)).trans ((hx i hq).2))) -- parser
   unfold measureV distV; rw [← pow_mul]; apply pow_le_pow_right₀ hw; have hF:1≤ k:=(le_max_left ..).trans hp
   calc
       _ ≤ (4*k)^a*D:=Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm a)
       _= k^a*(4^a*D):=by rw [mul_pow]; ring
       _≤ k^(a+1):=by rw [pow_succ]; exact Nat.mul_le_mul_left _ ((le_max_right ..).trans hp)
       _≤ _:=(pow_le_pow_right₀ hF hb)
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.lapsV
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.rateMeasure
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.priceL
