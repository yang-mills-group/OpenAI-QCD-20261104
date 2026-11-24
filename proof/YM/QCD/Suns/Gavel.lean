import YM.QCD.Suns.Mellow
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
-- publication.Evaluation
variable (hΓ: PassageR τ' D B S' b' χ g Ω X b₀ T₁ x κ s₀ 1 μ z 1 W' H A' (1/8) o)
variable (he:Invoice g Q.table V₁ T₁ σ η α D Λ)
variable (hX:∀ u,x≤u→Shade O.L τ'.t u) (hk:O.Branches T'.bind su)(hN:Even N)
abbrev finC (O:Patch)(B:SparkMesh)(j k:ℕ):Side:= B.n k* O.L^j
lemma powerV (O:Patch)(m k:ℕ): (finC O B (m+1) k).val=(finC O B m k).val*O.L.val:=by unfold finC; simp [pow_succ,mul_assoc]
abbrev RushK (O:Patch)(B:SparkMesh)(k j:ℕ)(T: Teller su): StepData (finC O B j k) (finC O B (j+1) k):=(Pike O 0).visit T.bind (powerV B O j k)
variable {t σ' v' θ:ℝ}
set_option quotPrecheck false
local notation "B!"=> towerQ O B n i k
local notation "C!"=>towerQ O B n (i+1) k
include hG hΓ hX he hk hN
lemma forever (h:i<n)(j:ℕ)(hy:n-(i+1)=j)(M₀:Voice (C!) N)(hp:TokenQ (P':=P') (X:=X) (V:=V) (U:=U) (r:=τ'.t) (x:=x) B b' g A0 M₀ t) (E:Voice (B!) N)(hU:TokenQ (P':=P') (X:=X) (V:=V) (U:=U) (r:=τ'.t) (x:=x) B b' g A0 E u)
   (hh:0< θ)(hE:EvalsG (C!) O.L (passportM O.J O.order_cut) T' b' Ω a d Λ (2*hatG O n (i+1) x) (rangeG O n (i+1) κ τ'.t x) (delay O n (i+1) x) τ'.t θ) (F': Forest (RushK O B k j T').ratio) (hf:0<y)(hr:y≤ Fare.solar F' Q.table (V i))(hv:0<v')(hC:t*v'≤ (Cvol (A0 (i+1))).re): 0<τ'.X.Q ∧ u*((gain (1/4) (finC O B j k) N) * (glossy (RushK O B k j T') τ' o F' O.L y (delay O n (i+1) x) / θ * v')) ≤ (Cvol (A0 i)).re:=by -- edit
    obtain ⟨hw,hT⟩:= voltU B g b' A0 hG hk hN h; have hz:=hG.vocals i h; have hu :0 < hatG O n i x:=(hX _ (matters ..)).value
    let V₀:=finC O B j k; let S:=Pike O i; let ℓ: (B!).val=(C!).val*O.L.val:= lift0 B h
    have he₁: C! = finC O B j k:=by unfold towerQ; rw [feetM,hy]
    have he₂ : B! = finC O B (j+1) k:=by unfold towerQ; rw [feetM,show n-i=j+1 from (by omega)]
    let C₁:= glossy (RushK O B k j T') τ' o F' O.L y (delay O n (i+1) x)
    have hz (c f:Side)(hc:c=finC O B j k)(hv:f=finC O B (j+1) k)(hp:f.val=c.val*O.L.val):∃ F:Forest (S.visit T'.bind hp).ratio, y ≤ Fare.solar F Q.table (V i) ∧ C₁= glossy (S.visit T'.bind hp) τ' o F O.L y (delay O n (i+1) x):=by subst c f; exact ⟨F',hr,rfl⟩
    obtain ⟨F,hF,h₁⟩:= hz (C!) (B!) he₁ he₂ ℓ; obtain ⟨hh',hH⟩:= stork B b' g A0 hG hΓ h E hU hu F hf hF; rw [← h₁] at hH; have hp' : u*C₁ / θ ≤ t:= (div_le_iff₀ hh).2 (hH.trans (preSun B b' g A0 hG h M₀ hp hE he hX 1))
    rw [hT]; simp only [Complex.smul_re,smul_eq_mul]; let Z:= gain (1/4) V₀ N; have hΩ:0 ≤ Z:=pow_nonneg (by norm_num: 0 ≤ (1/4:ℝ)) _; have hb: Z ≤ gain (Wv i)⁻¹ (C!) N:=by unfold Z V₀; rw [← he₁]; apply pow_le_pow_left₀ (show (0:ℝ) ≤1/4 from by norm_num); rw [one_div]; exact inv_anti₀ hw (hG.vocals i h).2.1
    have hq:0≤ (Cvol (A0 (i+1))).re:=(mul_pos hp.1 hv).le.trans hC
    refine ⟨hh',?_⟩; apply le_trans _ (mul_le_mul_of_nonneg_right hb hq); change u*(Z*(C₁/θ*v')) ≤ Z*(Cvol (A0 (i+1))).re; rw [show u*(Z*(C₁/θ*v'))=Z*(u*C₁/θ*v') from (by ring)]; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hp' hv.le).trans hC) hΩ
end Rails
end YM.QCD.Acre
