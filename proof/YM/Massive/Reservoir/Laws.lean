import YM.Massive.Sharp.Spectrum

/-! Quantitative pressure arithmetic for budget tests. IMPORTANT distinction
between pointwise and prior-integral caps on the normalized Pixel: here we
keep the four missing edges in the ratio of the volumes for integrated
height. (`YM.SectorNext.VACUUM_NORMALIZATION.Thermal` of baseline, now for marked QCD
and both directions.) `Audience` has a large power; floors keep it here.
Cost in `log g` in the integral price is NOT volume extensive.
-/
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
abbrev ηup := X.big*((2:ℝ)/strength T.top.clip)^su.lieDim
abbrev ηdown := X.small*Real.exp (-(T.bind.penalty*2))
lemma yu : 0<ηup X T:= mul_pos (zero_lt_one.trans_le X.big_ge) (pow_pos (div_pos (by norm_num) (strength_pos _)) _)
lemma yd : 0<ηdown X T:= mul_pos X.positive (Real.exp_pos _)
lemma rich_c (c:Side): (rich c:ℝ) ≤ 3*Fintype.card (Site c):= by
      unfold YM.SectorNext.Vacuum.rich; exact_mod_cast (Nat.sub_le (3*Fintype.card (Site c)) 3)
lemma spare_c (c:Side): (spare c:ℝ) ≤ 4*Fintype.card (Site c):= by
      unfold YM.SectorNext.Vacuum.spare; have hc: (0:ℕ)<Fintype.card (Site c):=Fintype.card_pos; have hp:3*Fintype.card (Site c)+1≤4*Fintype.card (Site c):=by omega
      exact_mod_cast hp
variable (c:Side)(J:Patch)(y a b:ℝ)
local notation "♯"=> (Fintype.card (Site c):ℝ)
local notation "gp"=> gaugeSize J.L y -- existing `q` reserved? collision avoid
variable (ht:0<gaugeSize J.L y)
include ht
lemma expUp : Real.log (ζMax X T c J.L y a) = ♯ * a + (YM.SectorNext.Vacuum.rich c:ℝ) * (Real.log (ηup X T) + ζd * Real.log gp):=by
    let g:=gp; have hp: X.big * (2*g/strength T.top.clip)^su.lieDim = ηup X T*g^su.lieDim:=by rw [show 2*g/strength T.top.clip=2/strength T.top.clip*g from (by ring),mul_pow, ← mul_assoc]
    unfold ζMax Globe.expo; rw [hp, Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ (mul_ne_zero (yu X T).ne' (pow_ne_zero _ ht.ne'))),Real.log_pow,Real.log_exp, Real.log_mul (yu X T).ne' (pow_ne_zero _ ht.ne'),Real.log_pow]; ring -- g defeq in log ring unfold
lemma expDown : Real.log (ζMin X T c J.L y b)= -♯ * b + spare c * (Real.log (ηdown X T) + ζd * Real.log gp):=by
    let g:=gp; have hp:X.small*g^su.lieDim*Real.exp (-(T.bind.penalty*2))=ηdown X T*g^su.lieDim:=by unfold ηdown; ring
    unfold ζMin Globe.expo; rw [hp, Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ (mul_ne_zero (yd X T).ne' (pow_ne_zero _ ht.ne'))),Real.log_pow,Real.log_exp,Real.log_mul (yd X T).ne' (pow_ne_zero _ ht.ne'),Real.log_pow] -- g
omit ht
abbrev shelfPrice (a b:ℝ):=a+b+2+(3* |Real.log (ηup X T)|+4* |Real.log (ηdown X T)|)
include ht
/-- Upper ratio (prior-integral price). Constant part times volume PLUS
  `4 d log(1/g)`. -/
lemma ratioL : Real.log (ζMax X T c J.L y a/ζMin X T c J.L y (b+2)) ≤ ♯ * shelfPrice X T a b + 4*ζd * (- Real.log gp):=by
    rw [Real.log_div (maxP J.L X ht|>.ne') (minP J.L X ht|>.ne'),expUp X T c J y a ht,expDown X T c J y (b+2) ht]
    have hh (x w v:ℝ)(ht:0 ≤ v)(hv:v≤w):v*x ≤ w*|x|:= le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) ht) (mul_le_mul_of_nonneg_right hv (abs_nonneg _))
    have hg:= congr_arg (fun t:ℕ=> (t:ℝ)*ζd*Real.log gp) (YM.SectorNext.Vacuum.spare_four c); unfold shelfPrice; push_cast at hg;
    have he:= hh (-Real.log (ηdown X T)) _ _ (show 0≤ (spare c:ℝ) from by positivity) (spare_c _); rw [abs_neg] at he
    nlinarith only [he,hh (Real.log (ηup X T)) _ _ (by positivity) (rich_c c), hg]
omit ht
/-- Coarser **pointwise** price does have a volume cost scaling like log(1/g). -/
abbrev penPrice (P:Patch)(y a:ℝ):=a + 3* |Real.log (ηup X T)+ ζd * Real.log (gaugeSize P.L y)|
abbrev keg (P:Patch)(y a b:ℝ):=21*(shelfPrice X T a b +4*ζd* |Real.log (gaugeSize P.L y)|)- (2*a-penPrice X T P y a)
include ht
lemma entrance : Globe.expo (keg X T J y a b) c ≤ Audience c X T J y a b:=by
    let r:= ζMax X T c J.L y a; let u:=ζMin X T c J.L y (b+2)
    have hr:0<r:=maxP J.L X ht; have hu:0<u:=minP J.L X ht; let d:=keg X T J y a b
    have hl : ♯ * (2*a-penPrice X T J y a) ≤ Real.log r:=by
         let g:= Real.log (ηup X T)+ ζd * Real.log gp
         unfold r penPrice; rw [expUp X T c J y a ht]; linarith only [mul_le_mul_of_nonneg_left (neg_abs_le g) (show 0 ≤ (rich c:ℝ) from Nat.cast_nonneg _), mul_le_mul_of_nonneg_right (rich_c c) (abs_nonneg g)]
    change Real.exp (-♯ *d) ≤ _; apply (Real.le_log_iff_exp_le (paid X ht|>.trans_le le_rfl)).mp -- name?
    change _ ≤ Real.log (r*(u/r)^21); rw [Real.log_mul hr.ne' (pow_ne_zero _ (div_ne_zero hu.ne' hr.ne')),Real.log_pow, Real.log_div hu.ne' hr.ne']
    have hq:= ratioL X T c J y a b ht; rw [Real.log_div hr.ne' hu.ne'] at hq; change Real.log r-Real.log u ≤ _ at hq; unfold d keg; have hv:(1:ℝ)≤ ♯:=by exact_mod_cast (show 1 ≤ Fintype.card (Site c) from Fintype.card_pos)
    have hz:0≤4*ζd:=by positivity
    rw [show (↑(21:ℕ):ℝ)=21 from by norm_num]; nlinarith only [hq,hl,mul_le_mul_of_nonneg_left (show -Real.log gp ≤ |Real.log gp| from neg_le_abs _) hz,mul_le_mul_of_nonneg_right hv (show 0≤4*ζd*|Real.log gp| from mul_nonneg hz (abs_nonneg _))]
-- Normalized prices
abbrev plaza (P:Pixel c N):= ∫ U,‖P U‖ ∂prior su c
include ht
lemma sheer_mark {P:Pixel c N}{z:ℝ}
    (hv : 0< Cvol P) (hp: z * Audience c X T J y a b ≤ (Cvol P).re)
    (hX: (∀ U,‖P U‖ ≤ z* major su c a (2*gp/strength T.top.clip) U) ∧ plaza c P ≤ z* ζMax X T c J.L y a) :
    (∀ U, ‖money P U‖ * Audience c X T J y a b ≤ major su c a (2*gp/strength T.top.clip) U) ∧ plaza c (money P) ≤ (ζMax X T c J.L y a/ζMin X T c J.L y (b+2))^21:=by
    let r:=(Cvol P).re; have h:0<r:=(Complex.lt_def.mp hv).1; let d:= Audience c X T J y a b; have hd: 0<d:= paid X ht
    have hh(z x y:ℝ)(hx:0≤x)(ht:z*d ≤ r)(HP:y≤z*x): r⁻¹*y*d ≤ x:=by
        rw [mul_assoc,inv_mul_eq_div]; apply (div_le_iff₀ h).mpr; exact (mul_le_mul_of_nonneg_right HP hd.le).trans (by nlinarith only [mul_le_mul_of_nonneg_right ht hx])
    have he'(U): ‖money P U‖=r⁻¹*‖P U‖ := (norm_smul _ _).trans (congr_arg (· * ‖P U‖) (Real.norm_of_nonneg (inv_pos.mpr h|>.le)))
    refine ⟨fun U=>by rw [he' U]; exact hh _ _ _ (Real.exp_pos _).le hp (hX.1 U),?_⟩
    let v:=ζMax X T c J.L y a; let u:=ζMin X T c J.L y (b+2); have hu:0<u:=minP J.L X ht; have hv:0<v:=maxP J.L X ht
    unfold plaza; simp_rw [he',integral_const_mul]; apply le_of_mul_le_mul_right _ hd; apply (hh _ _ _ hv.le hp hX.2).trans; change v ≤ (v/u)^21*(v*(u/v)^21); rw [mul_left_comm,← mul_pow,show v/u * (u/v)=1 by field_simp,one_pow,mul_one]
abbrev arm (P:Patch)(y a b:ℝ):= a+keg X T P y a b
lemma rooftop (P:Pixel c N)(hx: ∀ U, ‖P U‖ * Audience c X T J y a b ≤ major su c a (2*gp/strength T.top.clip) U) (U:Grid c): ‖P U‖ ≤ Globe.expo (- arm X T J y a b) c:=by
    have he: major su c a (2*gp/strength T.top.clip) U ≤ Globe.expo (-a) c:= Real.exp_le_exp.mpr (by rw [neg_mul_neg]; exact sub_le_self _ (sum_nonneg fun i _=>div_nonneg (Gauge.chord_nonneg ..) (div_nonneg (by positivity) (strength_pos ..).le)))
    let v:= keg X T J y a b; let z:= Globe.expo v c; let x:= arm X T J y a b; have hz:0<z:=Real.exp_pos _
    apply le_of_mul_le_mul_right _ hz; apply le_trans (mul_le_mul_of_nonneg_left (entrance X T c J y a b ht) (norm_nonneg (P U))); apply ((hx U).trans he).trans; apply le_of_eq; unfold arm z v; rw [←expoP]; congr 1; ring
lemma totalCap {P:Pixel c N}(h: plaza c P ≤ (ζMax X T c J.L y a / ζMin X T c J.L y (b+2))^21) :
    plaza c P ≤ Real.exp (21* (♯*shelfPrice X T a b + 4*ζd * (-Real.log gp))):=by
    let p:=ζMax X T c J.L y a / ζMin X T c J.L y (b+2); have hv:0<p:=div_pos (maxP J.L X ht) (minP J.L X ht); apply h.trans
    change p^21≤_; rw [← Real.exp_log (show 0<p^21 by positivity)]; apply Real.exp_le_exp.mpr; rw [Real.log_pow]; exact_mod_cast (mul_le_mul_of_nonneg_left (ratioL X T c J y a b ht) (show (0:ℝ)≤21 by norm_num)) -- p
end Reservoir
end Sharp
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Reservoir.entrance
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Reservoir.totalCap

