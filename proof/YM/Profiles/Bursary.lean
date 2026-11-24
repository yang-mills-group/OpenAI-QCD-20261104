import YM.Profiles.Proto
import YM.Profiles.Aurel
import YM.Massive.Reservoir.Laws
/-! # Work towards trajectory pressure under Mark: L1 majorants -/
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
namespace Sharp
namespace Rapture
open Price MassiveQCD.Sample MassiveQCD.Sample.Sail MassiveQCD.Plate Next.Rank IV Rain
open Massive.Pressure Reservoir
local notation "ζd"=> (su.lieDim:ℝ)
variable (Xb':HaarBudget su)
-- at patch fixed, allowed costs encompass coarse stops.M.Post *actual values* prediction path.Height.G or K values at least 1 and small.Spacing margin.Shape controls.For Gauge W.Total.Radius.Try.P. τ slope.User. req Use 1024 window constants.
noncomputable def riseC (t:Teller su)(J:Patch)(x a b:ℝ):ℝ:=keg Xb' t J x a b
variable (J:Teller su) (S:Patch) (θ w v y:ℝ)
lemma burner : Rate su S.L 0 (fun x:ℝ=>Real.log (gaugeSize S.L x)):=by
   let Q:=fun x:ℝ=>Real.log (gaugeSize S.L x); let F:=fun x:ℝ=>run S.L x; have hR:Rate su S.L 0 (fun x:ℝ=> Real.log (run S.L x)):=by
       intro b hb; have h:=(isLittleO_log_rpow_rpow_atTop (1:ℝ) hb).comp_tendsto (f:= _) (Work.E09.betaF_growth su S.L); filter_upwards [h.bound zero_lt_one,(Work.E09.betaF_growth su S.L).eventually_gt_atTop 1] with x hx he; have hf:0< betaF su x S.L:= by linarith only [he]
       simpa only [Function.comp_apply,one_mul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hf _),Real.rpow_one] using hx
   refine (hR.mul_left (-(1/2))).congr ?_; filter_upwards [Delay.shift_pos su S.L] with x hx; unfold gaugeSize; change Real.log _= _ * Real.log _; rw [Real.log_inv,Real.log_sqrt hx.le]; ring
lemma pricey : Rate su S.L 0 (fun x:ℝ=>riseC Xb' J S x w v):=by
     let G:=fun x:ℝ=>Real.log (gaugeSize S.L x); have hG:Rate su S.L 0 G:= burner S; have hx(f:ℝ→ℝ)(hf:Rate su S.L 0 f):Rate su S.L 0 (fun i=> |f i|):= Rate.compare hf (Eventually.of_forall fun x=>(abs_abs _).le)
     have hs := Rate.const (G:=su) (L:=S.L) (shelfPrice Xb' J w v)
     let F x:=w+3*|Real.log (ηup Xb' J)+ζd* G x|
     have hf: Rate su S.L 0 F:= Rate.add (Rate.const w) ((hx _ (Rate.add (Rate.const _) (hG.mul_left _))).mul_left _)
     let A i:=21*(shelfPrice Xb' J w v+4*ζd*|G i|); have ht :Rate su S.L 0 A:=(Rate.add hs ((hx _ hG).mul_left _)).mul_left _
     apply Rate.congr ((ht.add (Rate.const (- (2*w)))).add hf); apply Eventually.of_forall; intro i; change A i- (2*w-F i)= _; abel
variable (A E D C:ℝ)(M:ℕ)
local notation "Δ" x=>radiusB (run S.L x)
-- angle theta fixed. Appetite.
local notation "ξ" x=>Sail.roomAt S.L θ x
noncomputable def legendF (M:ℕ)(x:ℝ)(Z E K t:ℝ):= K + (Stags.bonus M (highR S.L x) (1/32)*Z+roomAt S.L θ x)+(E+ (taxK S.L x t)⁻¹)
noncomputable def fareUp (M:ℕ)(Kt Uv L Q B:ℝ) (x:ℝ):= legendF S θ M x Q Uv Kt ((2-1)/2)+riseC Xb' J S x L B
noncomputable def packN (L:Side)(x:ℝ)(M:ℕ):ℕ:= M*L.val*(radiusB (run L x))^2+1
lemma peakT (p q:ℝ)(M D' :ℕ):∀ᶠ x in atTop, |(packN S.L x D':ℝ)^4*fareUp Xb' J S θ M A E D p q x| ≤ betaF su x S.L ^ (1/2:ℝ):=by
     let H:=fareUp Xb' J S θ M A E D p q; let Z:=fun x:ℝ=>(packN S.L x D':ℝ)
     have hO:Jets.Touch.Seat S.L 0 (fun x :ℝ => (highR S.L x:ℝ)):=by -- name
           intro b hb; filter_upwards [Delay.monitor_pays su S.L 1 (D:=1) zero_le_one hb] with x hx; refine le_trans ?_ hx; unfold highR radiusB Delay.bill; rw [abs_of_nonneg (by positivity),one_mul,pow_one]; have h := Nat.ceil_lt_add_one (sq_nonneg (Real.log (betaF su x S.L))); linarith only [h,Nat.cast_nonneg (α:=ℝ) (Nat.ceil (Real.log x ^2))]
     have ht : Rate su S.L 0 Z:=by
         unfold Z packN; push_cast; apply Rate.add _ (Rate.const 1); have hh:=(hO.ruled.pow 2).mul_left ((D':ℝ)*(S.L.val:ℝ)); rw [zero_mul] at hh; exact hh
     have hv:Rate su S.L 0 H:=by unfold H fareUp legendF; refine Rate.add (Rate.add (Rate.add (Rate.const _) (Rate.add (((Sail.bumpedH S.L M (1/32)).ruled).mul_right _) ((slotR S.L θ).weaken (by norm_num)))) (Rate.add (Rate.const _) (Jets.Touch.couplings S.L (by norm_num : (0:ℝ)<(2-1)/2)))) (pricey Xb' J S D q)
     exact (Rate.mul (ht.pow 4) hv) _ (by norm_num)
end Rapture
end Sharp
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Rapture.peakT
