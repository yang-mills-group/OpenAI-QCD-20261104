import YM.Creno.Grant
import YM.Creno.Murr
import YM.Lust.Price
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
open Finset MintV Sapphire Talis
variable (L:Side)
local notation "νƒ" =>(7/8:ℝ)
local notation "Q" x:arg=> run L x
local notation "Zp" x:arg=>(run L x) ^ (7/8:ℝ)
local notation "λ₀"=>Real.log ((L.val):ℝ)
-- fuel wide
noncomputable def band (x:ℝ):ℕ:= ⌈Zp x⌉₊+32
variable {D:ℕ} (Hp:Dial D)
-- based on q-clock s'=riseV x nT; callers use at vintage.NOT MARK.P choose Pr extends. RHS p.A.rise spent.
noncomputable def globe (u:ℕ)(x:ℝ):ℝ:= (band L x+1:ℕ)*λ₀/(10000*((u:ℝ)+10))
noncomputable abbrev cash (u:ℕ)(x:ℝ):=Real.exp (globe L u x)
def mux (y:ℝ):ℕ:= 8000*(highR L y)^3+64
noncomputable def sc (y:ℝ):ℕ :=16*(highR L y)^3
local notation "j₀" => band L
local notation "ϱ"=>sc L
lemma mux_rate: Rate su L 0 fun y=>(mux L y:ℝ):= by unfold mux; push_cast; exact (((((base_rate L).pow 3).weaken (by ring_nf; try rfl)).mul_left _).add (Rate.const _))
lemma sx_rate: Rate su L 0 fun y=>(sc L y:ℝ):= by unfold sc; push_cast; exact ((((base_rate L).pow 3).weaken (by ring_nf; try rfl)).mul_left _)
lemma hgl (x:ℝ)(u:ℕ):0≤ globe L u x:=by unfold globe; exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast L.pos))) (by positivity)
lemma upq:Tendsto (fun x=>Zp x) atTop atTop:=(tendsto_rpow_atTop (by norm_num:(0:ℝ)<νƒ)).comp (Work.E09.betaF_growth su L)
lemma upb:Tendsto (band L) atTop atTop:= tendsto_atTop_mono (fun z=>Nat.le_add_right ⌈Zp z⌉₊ 32) (tendsto_nat_ceil_atTop.comp (upq L))
variable (hL:1<L.val)
lemma lifts : ∀ᶠ x in atTop,(band L x+1:ℕ) ≤ (2*(Zp x):ℝ):=by
     filter_upwards [(upq L).eventually_ge_atTop 34] with x hx; unfold band; push_cast; have hz:(↑⌈Zp x⌉₊:ℝ) < (Zp x)+1:=Nat.ceil_lt_add_one (by linarith only [hx]); linarith only [hx,hz]
-- any power ≤ν, divided by cap => vanish. literal
lemma par (a e b:ℝ)(hv:a<b)(he:0<e):∀ᶠ x in atTop,(run L x)^a ≤ e*(run L x)^b:=by
     filter_upwards [(Work.E09.betaF_growth su L).eventually ((tendsto_rpow_neg_atTop (show 0<b-a from sub_pos.mpr hv)).eventually_le_const he),Delay.shift_pos su L] with x ht hp
     change (run L x)^(-(b-a)) ≤e at ht; rw [show -(b-a)=a-b from (by ring), Real.rpow_sub hp,div_le_iff₀ (Real.rpow_pos_of_pos hp _)] at ht; exact ht
lemma band_w (ε:ℝ)(hε:0<ε):∀ᶠ x in atTop, (band L x+1:ℕ)≤ (ε*(run L x):ℝ):=by
     filter_upwards [par L νƒ (ε/2) 1 (by norm_num) (by positivity),lifts L] with x h1 h2; rw[Real.rpow_one] at h1; linarith only [h1,h2]
-- crews.H clocks any ≤station beta.LeadingReq.Gather equations fees. 
local notation "v!" y:arg=> highR L y
lemma brightLimits : ∀ᶠ x in atTop,∀ i,i ≤2*j₀ x+3→ riseV L x i ≤ x+(run L x) ∧ Q (riseV L x i)≤2*(run L x):=by
     let m:=su.slopeConstant*λ₀; have hm:0≤ m:= Work.E04.shift_nonneg su L
     have ht:0< m+1:=by linarith
     let c:=(3*(m+1))⁻¹; have hc:0<c:=by unfold c; positivity
     filter_upwards [band_w L c hc] with x hx i h; have h:(↑i:ℝ)≤ 3*(↑(band L x+1:ℕ):ℝ):=by exact_mod_cast (show _ from (show i ≤ 3* (band L x+1) from by omega))
     have he:(i:ℝ)*m ≤ run L x:=by
           refine le_trans ((mul_le_mul (h.trans (mul_le_mul_of_nonneg_left hx (by norm_num))) (show m ≤ m+1 from by linarith) hm (?_))) (le_of_eq ?_); · exact (Nat.cast_nonneg i).trans (h.trans (mul_le_mul_of_nonneg_left hx (by norm_num)))
           unfold c; field_simp <;> ring
     change x+i*m ≤ x+run L x∧ (x+i*m)+m ≤ 2*(x+m); change (i:ℝ)*m ≤ x+m at he; exact ⟨add_le_add_right he x,by linarith only [he]⟩
include hL
variable (d:ℕ)
lemma globe_top :Tendsto (globe L d) atTop atTop:=((tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun x=>Nat.le_succ _) (upb L))).atTop_mul_const (show 0<λ₀ from Real.log_pos (by exact_mod_cast hL))).atTop_div_const (by positivity)
lemma nop (a e:ℝ)(h:a<νƒ)(ht:0<e):∀ᶠ x in atTop,(run L x)^a ≤ e*globe L d x:=by
     let C:= (10000*((d:ℝ)+10)); let E:= e*λ₀/C; have h1:0<λ₀:= Real.log_pos (by exact_mod_cast hL); have hC:0<C:=(by unfold C; positivity); have hP:0<E:=by unfold E; positivity
     filter_upwards [par L a E νƒ h hP] with x hx
     have hB:(Zp x) ≤ (↑(band L x+1:ℕ):ℝ):= (Nat.le_ceil _).trans (Nat.cast_le.mpr (show _ ≤ _ from Nat.le_trans (Nat.le_add_right _ 32) (Nat.le_succ _)))
     exact hx.trans ((mul_le_mul_of_nonneg_left hB hP.le).trans_eq (by unfold globe E C; ring))
lemma fw (a e:ℝ)(h:0 ≤ a)(hw:a<νƒ)(ht:0<e):∀ᶠ x in atTop,∀ i≤2*j₀ x+3, Q (riseV L x i)^a ≤ e*globe L d x:=by
     let E:=(2:ℝ)^a; have hE:0<E:=Real.rpow_pos_of_pos (by norm_num) _
     filter_upwards [nop L hL d a (e/E) hw (by positivity), brightLimits L, aheadΩ L _ (Delay.shift_pos su L), Delay.shift_pos su L] with x hp hF hx hz i hi
     refine le_trans (Real.rpow_le_rpow (hx i).le (hF i hi|>.2) h) ?_
     rw [Real.mul_rpow (by norm_num:(0:ℝ)≤2) hz.le]; change E*_ ≤ _; apply (mul_le_mul_of_nonneg_left hp hE.le).trans; exact le_of_eq (by field_simp)
-- syntactic Pay under stencil paths.
lemma richNums (f:ℝ→ℝ)(he:Rate su L 0 f)(a:ℝ)(ha:0<a):∀ᶠ x in atTop,∀ i≤2*j₀ x+3, |f (riseV L x i)| ≤ a*globe L d x:=by
      filter_upwards [aheadΩ L _ (he (1/2) (by norm_num)),fw L hL d (1/2) a (by norm_num) (by norm_num) ha] with x hx hf i h; exact (hx i).trans (hf i h)
end Mistral
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Mistral.globe_top
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Mistral.mux_rate
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Mistral.richNums
