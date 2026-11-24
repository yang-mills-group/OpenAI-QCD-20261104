import YM.QCD.Suns.Horizon
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
open MeasureTheory
lemma sheer (X:Pixel c N)(hx:Continuous X)(hp:∀ U, ‖X U‖ ≤ w) : (Cvol X).re ≤ ‖peakW c N‖*w:=by
   let f:Grid c→ℂ:= fun i=>cBer X i; apply le_trans (Complex.re_le_norm _); apply (norm_integral_le_integral_norm f).trans; let g (_:Grid c):= ‖peakW c N‖*w
   apply (integral_mono (μ:=prior su c) (g:=g) (((peakW c N).continuous.comp hx).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _) (fun i=> ((peakW c N).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hp i) (norm_nonneg _)))).trans; simp [g]
noncomputable def FareV (n:Side)(k:ℕ):= ‖peakW n k‖
noncomputable def nugget (T:Policy Q T'.top N)(o:Target.Order su W)(O:Patch)(B:SparkMesh)(k j:ℕ)(s r p y x:ℝ):= (max 1 (FareV (finC O B (j+1) k) N*(s*r)/(glossy _ T o (hint O B k j T') O.L y (tallyK O.L x j)*p)))⁻¹ -- remove unused
lemma nugget_pos (T:Policy Q T'.top N) : 0 < nugget T o O B k j s₀ r u z x := inv_pos.mpr (zero_lt_one.trans_le (le_max_left ..))
set_option quotPrecheck false
local notation "B!"=> towerQ O B n i k
local notation "C!"=>towerQ O B n (i+1) k
variable {t θ s v':ℝ}
include hG hΓ hX he hk hN
lemma burn (h:i<n)(j:ℕ)(hy:n-(i+1)=j)(M₀:Voice (C!) N)(hp:TokenQ (P':=P') (X:=X) (V:=V) (U:=U) (r:=τ'.t) (x:=x) B b' g A0 M₀ t) (E:Voice (B!) N)(hU:TokenQ (P':=P') (X:=X) (V:=V) (U:=U) (r:=τ'.t) (x:=x) B b' g A0 E u)
   (hh:0< θ)(hE:EvalsG (C!) O.L (passportM O.J O.order_cut) T' b' Ω a d Λ (2*hatG O n (i+1) x) (rangeG O n (i+1) κ τ'.t x) (delay O n (i+1) x) τ'.t θ) (hm: ScoresU (k:=k) B (j+1) 0 T' a d Λ x b' Ω O κ τ'.t s)(hs:0<s) (hf:0<y)(hr:y≤ Fare.solar (hint O B k j T') Q.table (V i))(hv:0<v')(hC:t*v'≤ (Cvol (A0 (i+1))).re): nugget τ' o O B k j s θ v' y x ≤ Wv i:=by
    let F':= hint O B k j T'; obtain ⟨hw,hT⟩:= voltU B g b' A0 hG hk hN h; have hz:=hG.vocals i h; have hu :0 < hatG O n i x:=(hX _ (matters ..)).value
    let S:=Pike O i; let ℓ: (B!).val=(C!).val*O.L.val:= lift0 B h; have hY:n-i=j+1:=by omega
    have he₁: C! = finC O B j k:=by unfold towerQ; rw [feetM,hy]
    have he₂ : B! = finC O B (j+1) k:=by unfold towerQ; rw [feetM,hY]
    let C₁:= glossy (RushK O B k j T') τ' o F' O.L y (tallyK O.L x j)
    have hz (c f:Side)(hc:c=finC O B j k)(hv:f=finC O B (j+1) k)(hp:f.val=c.val*O.L.val):∃ F:Forest (S.visit T'.bind hp).ratio, y ≤ Fare.solar F Q.table (V i) ∧ C₁= glossy (S.visit T'.bind hp) τ' o F O.L y (delay O n (i+1) x):=by subst c f; refine ⟨F',hr,?_⟩; unfold delay; rw [hy]; rfl
    obtain ⟨F,hF,h₁⟩:= hz (C!) (B!) he₁ he₂ ℓ; obtain ⟨hh',hH⟩:= stork B b' g A0 hG hΓ h E hU hu F hf hF; rw [← h₁] at hH; have hp' : u*C₁ ≤ t*θ:= hH.trans (preSun B b' g A0 hG h M₀ hp hE he hX 1)
    have hf' :0<C₁:=by unfold C₁ glossy; positivity
    have hN' : Nonempty (Cove.Keys (C!) N):= ⟨Sum.inl ((0, Classical.arbitrary _),b')⟩
    let L₁:= FareV (finC O B (j+1) k) N; have hL : ‖peakW (towerQ O B n i k) N‖=L₁:= by rw [he₂]; rfl
    let g₁:= gain (Wv i)⁻¹ (towerQ O B n (i+1) k) N; have hg:0<g₁:=pow_pos (inv_pos.mpr hw) _
    have hb := sheer (A0 i) (firms B g b' A0 hG hk hN _ h.le).1 (preSun B b' g A0 hG h.le E hU (evalT B b' hY hm) he hX); rw [hL,hT] at hb; simp only [Complex.smul_re, smul_eq_mul] at hb; have hx: g₁*(t*v')≤ L₁*(u*s):=(mul_le_mul_of_nonneg_left hC hg.le).trans hb
    have hε: g₁ ≤ L₁*(s*θ)/(C₁*v'):=by
          apply (le_div_iff₀ (mul_pos hf' hv)).2; apply le_of_mul_le_mul_right _ hU.1; linarith only [mul_le_mul_of_nonneg_right hx hh.le,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp' hv.le) hg.le]
    unfold nugget; let y₁:=(Wv i)⁻¹; apply le_trans _ (inv_inv (Wv i)|>.le); apply inv_anti₀ (inv_pos.mpr hw); by_cases he:y₁≤1
    · exact he.trans (le_max_left ..)
    have hj:Fintype.card (Cove.Keys (C!) N)>0:=Fintype.card_pos; refine (le_trans (b:=g₁) ?_ hε).trans (le_max_right ..)
    unfold g₁ Rain.gain; rw [show Fintype.card (Cove.Keys (C!) N) = Fintype.card (Cove.Keys (C!) N)-1+1 from (by omega),pow_succ']; exact le_mul_of_one_le_right (inv_pos.mpr hw|>.le) (one_le_pow₀ (le_of_not_ge he))
variable (hZ: TokenZ (P':=P') (X:=X) (V:=V) (U:=U) (τ':=τ') (x:=x) B b' g A0 n t)
variable (K₀ Y₀ Q₀ : ℕ→ℝ) (hv:∀ j,K₀ j>0) (hp:Winged O T' Q τ' o B k x t K₀ Y₀ Q₀) (hP:∀ j,ScoresU (k:=k) B j 0 T' a d Λ x b' Ω O κ τ'.t (K₀ j))
include hv hp hP hZ
lemma prairie (h:i<n)(hx:n=i+(j+1)): nugget τ' o O B k j (K₀ (j+1)) (K₀ j) (Y₀ j) (Q₀ j) x ≤ Wv i:=by
   obtain ⟨F,u,hU,hQ⟩:= (pursuit B b' g A0 hG hΓ he hX hk hN K₀ Y₀ Q₀ hv hp hP hZ j (i+1) (by omega)).costs
   obtain ⟨hV,hL,hh,Z,v,hp',hΓ',hR⟩:= hG.costs i h.le; have hΨ:delay O n i x=tallyK O.L x (j+1):=by unfold delay; rw [show n-i=j+1 from (by omega)]
   exact burn B b' g A0 hG hΓ he hX hk hN h j (by omega) F hU Z ⟨hp',hΓ',hR⟩ (hv j) (evalT B b' (by omega) (hP j)) (hP (j+1)) (hv _) (hp.yay j) (by have hx := hV; unfold Cashroom hatG at hx; rw [hΨ] at hx; exact hp.rate j _ hx.1 hx.2) (hp.yes j) hQ
end Rails
end YM.QCD.Acre
