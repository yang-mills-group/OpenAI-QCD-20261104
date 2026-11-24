import YM.Massive.Glint.Gleam
/-! # Why the marked density has positive germ body: preserve reality under transport with Wilson phase and a gain-trajectory marker. -/
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
open Next.Rank IV Rain
namespace Glint
open High.PrismT Globe Massive.Reading
variable (L1:HaarBudget su)(F':ℂ→Pixel c N)(D':PathData su)
variable {hj:J.Branches T'.bind su}{K1 b₁ b₂ p:ℝ}
variable (Y:∀ j,LanternT (towerQ J B n 0 k) N (towerQ J B n j k)) (hP:Regular L1 (1/2) K1 b₂ T' Q B F₀ x κ τ g Pt E (fun i=> g.costP i+N*Xb i) D W' k V1 U1 W1 Q1) -- common θ fix
variable (hk: CarrierL J.L T'.top N ε D0 A3 a3 Q₀)(hC:Sharp.Purer T' J Ω N x τ.t a d Λ κ ε D0 b₁)(hp: Gallery T' J n k B N V1 W1 Q1 Y hj)
variable (hw: Fueled T' B F₀ M₀ V1 U1 g Pt E τ.t x ε D0 k Y p v)(ht:Sharp.Attendance F₀ M₀ B Y τ.t D0 ε b₁ b₂ w v E Pt T' V1 U1 L1 x g)
open Sharp
local notation "sY"=>ShapeX B Y M₀.tip v
local notation "qX"=> gainsW B Y M₀ τ.t x
local notation "φ"=>Rotary.chartR
local notation "Φ!"=> S.visit K h
-- pin negative Hess.Body via actual Regal (gamma5-reality) at all physical mass markers.
lemma primalP (X:Pixel c N)(he:∀ U, Cove.light _ (X U)=primalD c N β b U)(U: Grid c): Regal c N (X U)=X U:=by
    let T:=copies N (bareD 0 U b); let Y:= idol c N; have hL : star Y*Y=1:=white.1
    have hK : star T=Y*T*star Y:=by unfold T Y idol; rw [← copies_star, ← copies_star,chi_star, ← copies_mul, ← copies_mul, gamma5] -- maybe rw order
    apply Subtype.ext; change disguise Y (surf _ (Cove.light _ (X U)))=Cove.light _ _; rw [he]; change disguise Y (surf _ ((bare β U:ℂ) • gauss T))=((bare β U:ℂ) • gauss T); rw [map_smulₛₗ,map_smul]; rw [starRingEnd_apply, show star (bare β U:ℂ)=(bare β U:ℂ) from Complex.conj_ofReal _]; apply congr_arg
    unfold gauss; rw [Globe.surfS,map_weight]; apply congr_arg; rw [Port.surf_form, hK,disguise,form_map,Matrix.transpose_transpose]; -- hK matching T
    congr 1; simp only [Matrix.mul_assoc,hL,mul_one]; rw [← Matrix.mul_assoc (star Y),hL,one_mul]
section travel
lemma surfs (X:Lanes f N) (hX:∀ i, Regal f N (X i)=X i) (V:Grid f):
 disguise (idol c N) (surf _ (can S h N X V)) = can S h N X V:=by
   let A:= choir N (tied S h 0 V); let Q:= tied S h 0 V
   have hA:idol c N*A*star (idol f N)=A:=by unfold A idol; rw [← copies_star,← replicas,← replicas,← choir_mul,← choir_mul]; congr 1; change chirality c * Q * star (chirality f)=Q; have he:chirality c*Q=Q*chirality f:= Eq.symm (tiedSpin ..); rw [he, Matrix.mul_assoc,chi_star,chi_sq,Matrix.mul_one]
   have hv:=Kit.compat (Sway.white (F:=N) (f:=f)) (Sway.white (F:=N) (f:=c)) 1 A (surf _ (Cove.light _ (X V))); rw [hA,← Globe.shoot, show disguise _ (surf _ (Cove.light _ (X V)))= Cove.light _ (X V) from congr_arg Subtype.val (hX V)] at hv; exact hv
lemma lumin (hw:S.patch.Branches K su)(X:Lanes f N) (hX:∀ i, Regal f N (X i)=X i) (V:Grid c): let Y:= Kin.travel N w S K h β hw X; Regal c N (Y V)=Y V:=by
    intro Y; change Regal c N (wearK c N w (fort S K h N β X V))= _; rw [dearR]; apply congr_arg (wearK c N w); apply Subtype.ext; change disguise _ (surf _ (Cove.light _ (fort S K h N β X V)))=Cove.light _ (fort S K h N β X V); rw [pureShift N S K h β hw]
    let D:=(rib (Modes c N)).toAddMonoidHom.toRealLinearMap (surf_cont (Modes c N)); let A:=disguise (idol c N); let Z:Fields c N →L[ℝ] Fields c N:= (A.toLinearMap.toContinuousLinearMap.restrictScalars ℝ).comp D -- continuouslinear yes?
    let F U:=(Φ!).density β U V • can S h N X U; change Z (∫ U,F U ∂prior su f)=_; rw [← Z.integral_comp_comm (honor N S K h β hw X V)]; refine integral_congr_ae (ae_of_all _ fun i=>?_); dsimp only; rw [map_smul]; exact congr_arg ((Φ!).density β i V • ·) (surfs X hX i)
end travel
include hp hP
lemma rulesX (z:ℝ) (hi:i≤n) (U:Grid (towerQ J B n i k)): Regal (towerQ J B n i k) N (ShapeX B Y M₀.tip v i z U)=ShapeX B Y M₀.tip v i z U:=by
    let c(i):=towerQ J B n i k; let X Q:= Q1 0 Q; let F:= Aperture.ingredient (c 0) M₀.tip; let Z:= exp (((v:ℂ)*(z:ℂ)) • F); let P(i):= Regal (c i) N; unfold ShapeX; induction i with
    | zero=>
         change P 0 (sY 0 z U)=(sY 0 z U); rw [show sY 0=Aperture.spun (Q1 0) v M₀.tip from flare B hj Y hp _ v] -- LHS? notation
         have hr: P 0 F= F:=by unfold F Aperture.ingredient; rw [map_sum]; exact sum_congr rfl fun i _=> (Pith.rentCross (c 0) _).real i _
         have hX:P 0 Z= Z:=by
              rw [show Z=exp (((v*z):ℝ) • F) from ?_, NormedSpace.map_exp (P 0) (Sway.OrbitG.phare _), eSM (P 0) (Sway.OrbitG.phare _) (v*z), hr]; unfold Z; rw [← Complex.ofReal_mul,Complex.coe_smul]
         change P 0 (Q1 0 U*Z)=_; rw [map_mul,hX]; exact congr_arg (· * Z) (primalP (Q1 0) hP.begin U)
    | succ i ih=>
         rw [hp.progresses i hi]; exact lumin (S:=Pike J i) (h:=lift0 (t:=k) B (show i<n from hi)) hj (Y i Z) (fun i=> ih (by omega) i) U
end Glint
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Glint.rulesX
