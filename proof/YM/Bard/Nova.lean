import YM.Massive.Reservoir.Laws
import YM.Bard.Norms
import YM.Profiles.Permeate
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
open Price Next.Rank IV Rain
open Massive.Pressure
open YM.SectorNext.Vacuum (rich spare)
variable (X:HaarBudget su)
variable (Y:∀ j,LanternT (towerQ J B n 0 k) N (towerQ J B n j k)) (hj:J.Branches T'.bind su)(hE:Gallery T' J n k B N V1 W1 Q1 Y hj)
variable {R0 K₁ B₁ p:ℝ}
variable (hw:Fueled T' B F₀ M₀ V1 U1 g Pt E τ.t x ε D0 k Y p v) -- p type nb
local notation "sY"=> ShapeX B Y M₀.tip v
local notation "qX"=> gainsW B Y M₀ τ.t x
variable (hk:CarrierL J.L T'.top N ε D0 A3 a3 Q₀) (hP:Regular X t R0 K₁ T' Q B F₀ x κ τ g Pt E (fun i=> g.costP i+N*Xb i) D W' k V1 U1 W1 Q1)
open scoped ComplexOrder


namespace Reservoir
variable (T:Teller su)
local notation "ζd"=> (su.lieDim:ℝ)
open MeasureTheory
variable (c:Side)(J:Patch)(y a b:ℝ) {s z B D:ℝ}
local notation "gp"=>gaugeSize J.L y
local notation "κ₀"=>ζMax X T c J.L y a
local notation "κ₁"=>ζMin X T c J.L y (b+2)
local notation "♯"=> (Fintype.card (Site c):ℝ)
-- path pressure integrated. No integrable condition on Z required. Exact therapy
abbrev manaV (a b D z:ℝ):=D+z-a+21*shelfPrice X T a b
variable (ht:0<gaugeSize J.L y)
include ht
lemma coinsV (D z:ℝ) : ζMax X T c J.L y (D+z) ≤ Real.exp (♯ * manaV X T a b D z + 21*(4*ζd*(-Real.log gp)))*Audience c X T J y a b:=by
    have hu:0<κ₀:= maxP J.L X ht; have hv:0<κ₁:=minP J.L X ht
    let i:= manaV X T a b D z; apply (Real.log_le_log_iff (maxP J.L X ht) (mul_pos (Real.exp_pos _) (paid X ht))).mp
    have h:=ratioL X T c J y a b ht; rw [Real.log_div hu.ne' hv.ne'] at h
    rw [Real.log_mul (Real.exp_pos _).ne' (paid X ht).ne',Real.log_exp]; change _ ≤ _+ Real.log (κ₀*(κ₁ / κ₀)^21); rw [Real.log_mul hu.ne' (pow_ne_zero _ (div_ne_zero hv.ne' hu.ne')),Real.log_pow, Real.log_div hv.ne' hu.ne',show (↑(21:ℕ):ℝ)=21 by norm_num]; unfold manaV
    have hx: Real.log (ζMax X T c J.L y (D+z)) = Real.log κ₀ + ♯*(D+z-a):=by rw [expUp X T c J y (D+z) ht,expUp X T c J y a ht]; ring
    rw [hx]; linarith
lemma majorMoreV (d z:ℝ)(U:Grid c): Massive.Pressure.major su c d (2*gp/strength T.top.clip) U*Real.exp (♯*z) = Massive.Pressure.major su c (d+z) (2*gp/strength T.top.clip) U:=by unfold Massive.Pressure.major; rw [← Real.exp_add]; congr 1; ring
open Massive
lemma entersV (D z:ℝ)(v:Density c N)(Z:ℝ) (u:Density c N)
    (hz:0 < joint u)(hZ:0 ≤ Z) (hs:1 < c.val)
    (hK: Z * Audience c X T J y a b ≤ (joint u).re)
    (hx:∀ U, ‖v U‖ ≤ Z*(major su c D (2*gp/strength T.top.clip) U *Real.exp (♯ * z))) :
      ‖joint v / joint u‖ ≤ Real.exp (♯ * manaV X T a b D z +21*(4*ζd*(-Real.log gp))):=by
    let μ(U:Grid c):= Grass.ber _ (v U)
    let i:= manaV X T a b D z; let r:=4*ζd*(-Real.log gp); let w:=Real.exp (♯ * i+21*r)
    let fU:=major su c (D+z) (2*gp/strength T.top.clip); let p':=prior su c
    obtain ⟨hZt,hψ⟩:= Complex.lt_def.mp hz; have hr':(joint u).re > 0:=hZt; have hr:joint u=((joint u).re:ℂ):=Complex.ext (by simp) hψ.symm; have hn:‖joint u‖=(joint u).re:=(congr_arg Norm.norm hr).trans (normS _ hr'.le); rw [norm_div,hn]; apply (div_le_iff₀ hr').mpr
    have htF:0<2*gp/strength T.top.clip:=div_pos (mul_pos (by norm_num) ht) (strength_pos _)
    have hx' := integral_major X (D+z) htF hs; let F:=Audience c X T J y a b; have hF:0<F:=paid X ht
    change ‖∫ U,μ U ∂p'‖≤ _; have hh:Integrable fU p':= (major_cont ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
       _≤ ∫ U,‖μ U‖ ∂p':= norm_integral_le_integral_norm _
       _≤ ∫ U,Z*fU U ∂p':= integral_mono_of_nonneg (Eventually.of_forall fun i=>norm_nonneg _) (hh.const_mul _) (Eventually.of_forall fun U=>((Grass.price _).trans ((hx U).trans_eq (congr_arg _ (majorMoreV _ _ _ _ ht D z U))))) -- Goal maybe Integral Energy status; name. fix args.
       _= Z * ∫ U,fU U ∂p':= integral_const_mul _ _
       _≤ Z*ζMax X T c J.L y (D+z):=mul_le_mul_of_nonneg_left (hx'.trans_eq (by unfold ζMax Globe.expo; rw [neg_mul_neg])) hZ
       _≤ Z * (w * F):= mul_le_mul_of_nonneg_left (coinsV X T c J y a b ht D z) hZ
       _≤ _:= by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hK (by unfold w; positivity)
lemma levelV (N D z A3:ℝ)(hV:manaV X T a b D z +1 ≤ N)(hv:21*(4*ζd*(-Real.log gp)) ≤ ♯) (hz:A3≤ Real.exp (♯ * manaV X T a b D z +21*(4*ζd*(-Real.log gp)))): A3 ≤ Real.exp (♯*N):=by apply hz.trans (Real.exp_monotone ?_); change _ ≤ ♯*N; linarith only [hv, mul_le_mul_of_nonneg_left hV (by positivity :0 ≤ ♯)]
end Reservoir
end Sharp
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Reservoir.entersV
