import YM.QCD.Disc.Lucid
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
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
namespace Rails
variable {θ ε p:ℝ} (L:Side)(θ ν:ℝ)
open Jets.Sun
abbrev lapF (N:ℕ):=fareG 1 1 N
lemma received (N:ℕ) : 1 ≤ lapF N:=by
  unfold lapF fareG; have h : 0 ≤ Brick.stemF N:=by unfold Brick.stemF Jets.Sun.fingers; positivity
  linarith
lemma scaleF (N:ℕ)(u:ℝ): fareG 1 u N=(lapF N)*u:=by unfold lapF fareG; ring
def eraF (N:ℕ):= (lapF N)^2*2
lemma earns (N:ℕ):1≤eraF N:=by have h:=one_le_pow₀ (received N) (n:=2); unfold eraF; linarith
lemma latch (hθ:0<θ)(N:ℕ): ∀ᶠ x in atTop, let w:= highW L (eraF N) θ (run L x); let t:=speedP L θ x
   1 ≤ t ∧ t ≤ fareG 1 t N ∧ fareG 1 t N ≤ w ∧fareG 1 (fareG 1 t N) N ≤ w:=by
    filter_upwards [framesC L θ hθ] with x hx; intro w t; have hp:=received N; have hL:=hx.2.1
    have he:1 ≤ t:=by unfold t speedP; linarith
    have hv : t ≤ fareG 1 t N:=by rw [scaleF]; exact le_mul_of_one_le_left (by linarith) hp
    have hd : fareG 1 t N ≤ fareG 1 (fareG 1 t N) N:=by nth_rw 2 [scaleF]; exact le_mul_of_one_le_left (zero_le_one.trans (he.trans hv)) hp -- tactic
    have hh : fareG 1 (fareG 1 t N) N ≤ w:=by rw [scaleF,scaleF]; unfold t w highW run speedP eraF; nlinarith only [mul_le_mul_of_nonneg_left hx.2.2.2 (sq_nonneg (lapF N))]
    exact ⟨he,hv,hd.trans hh,hh⟩
lemma beamsR : Rate su L (-1) (roofK L θ ν):=by
    let t:= chip_r L θ; have h:=((chip_rate L).mul t.ruled).mul_left (ν*(4:ℝ)⁻¹/(L.val:ℝ)); rw [add_zero] at h
    refine h.congr (Eventually.of_forall fun i=>?_); unfold roofK Emax speedP rust; have hp:= fan_pos L θ i; field_simp
    all_goals ring
lemma turf (he:0<ν) : ∀ᶠ x in atTop,0 < roofK L θ ν x ∧ roofK L θ ν x ≤1∧ roofK L θ ν x ≤ wink L x:=by
   have h:Rate su L (-(1/2)) (Port.wink L):=Rate.power; have hh:=beamsR L θ ν
   -- compare via multiply beta
   have hm:= hh.mul (Rate.power (a:= (1/2:ℝ))); filter_upwards [hm.below (by norm_num) 1 zero_lt_one, hh.below (by norm_num) 1 zero_lt_one, event_chip L θ] with x hx hk hQ
   have he' :0 < roofK L θ ν x:=by unfold roofK Emax speedP; have ht:=hQ.2.1; have hg:= fan_pos L θ x; positivity
   refine ⟨he',(le_abs_self _).trans hk,?_⟩
   unfold Port.wink; rw [Real.rpow_neg hQ.1.le,← one_div]; apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ.1 _)).mpr; exact (le_abs_self _).trans hx
lemma slopes : ∀ᶠ x in atTop, haloK L (run L x) ≤ haloK L x:=by
   filter_upwards [Delay.shift_pos su L] with x hx
   have ht:= hugs L (run L x); unfold haloK; exact Real.rpow_le_rpow_of_nonpos hx ht (by norm_num)
-- at x crop apex as Needed.
lemma wakeR (q:Stage)(ht:q.clip.direct≤1)(b W:ℝ)(hb:0<b)(M:ℕ):∀ᶠ x in atTop,∀ R:BudgetPoint, Kites.Now L R q x→ let t:=run L x
  R.threshold=temp t∧ R.B=radiusB t∧Decent q.clip R ∧R.threshold ≤2*fiery su t L ∧W ≤ loopBill su L t ∧ M ≤ R.B∧ R.threshold ≤ b:=by
   have hp:=Work.E09.betaF_growth su L; -- Folio.outings needs Patch
   have hX : ∀ᶠ x in atTop, temp x ≤2*fiery su x L:=by
       have hT : Tendsto (fun x=> fiery su x L/temp x) atTop (𝓝 1):= Work.E09.temp_ratio _
       filter_upwards [eventually_gt_atTop (0:ℝ), hT.eventually (le_mem_nhds (by norm_num : (1:ℝ)/2<1))] with x hx h
       linarith [(le_div_iff₀ (Work.E09.temp_pos hx)).mp h]
   filter_upwards [hp.eventually (plusT q ht),hp.eventually hX,hp.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop M),hp.eventually ((Touch.Seat.your L).eventually_ge_atTop (W/2)),(Rate.flame (G:=su) (L:=L)).below (by norm_num) b hb] with x hx hf hh hL hV R hR t
   have he : R.threshold = temp (betaF su x L):= hR.baseG
   refine ⟨he,hR.ball,(hx _ hR.era.2.2.symm hR.ball he).1,(he ▸ hf),?_ , hR.ball.symm ▸ hh,hR.baseG.symm ▸ ((le_abs_self _).trans hV)⟩
   change W/2 ≤ (Delay.fineMonitor su L t) at hL; unfold ConnectedActivityE6.loopBill; linarith
end Rails
end YM.QCD.Acre
