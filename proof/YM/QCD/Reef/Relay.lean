import YM.QCD.Reef.Urn
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
namespace IV
open Globe
lemma sailsK (Q) (K:Policy Q T'.top N)(V V' :ℕ→ℝ)(hv:∀ (B:SparkMesh)(k i:ℕ),let u:=run O.L (tallyK O.L x (i+1));∀ p:ℝ,u/2 ≤ p→ p≤ 2*u →TourV V' O B k i ≤ Fare.solar (hint O B k i T') Q.table p)(o':Target.Order su W)(u:ℝ) :∃ Z:ℕ→ℝ,∀ (B:SparkMesh)(k:ℕ),Winged O T' Q K o' B k x (expo u (finC O B 0 k)) (TourV V O B k) (TourV Z O B k) (TourV V' O B k):=by
    let Y:ℕ→ℝ := Nat.rec u (fun j z=> (-(leafZ N*Real.log (1/4))+ (toga K o' O (V' j) (tallyK O.L x j)-V j+z))/bear O.L)
    refine ⟨Y,fun B k=>⟨fun _=>Real.exp_pos _,rfl,fun _=>Real.exp_pos _,hv _ _,fun i he=>?_⟩⟩; rw [gainQ B O V V' Y K he]; unfold TourV; rw [tour_c]; congr 1; rw [mul_comm]; exact div_mul_cancel₀ _ bear_pos.ne'
set_option quotPrecheck false
local notation "B!"=> towerQ O B n i k
local notation "C!"=>towerQ O B n (i+1) k
variable {t θ s v':ℝ}
include hG hΓ hX he hk hN
lemma burnK (h:i<n)(j:ℕ)(hy:n-(i+1)=j)(M₀:Voice (C!) N)(hp:TokenQ (P':=P') (X:=X) (V:=V) (U:=U) (r:=τ'.t) (x:=x) B b' g A0 M₀ t) (E:Voice (B!) N)(hU:TokenQ (P':=P') (X:=X) (V:=V) (U:=U) (r:=τ'.t) (x:=x) B b' g A0 E u)
   (hh:0< θ)(hE:EvalsG (C!) O.L (passportM O.J O.order_cut) T' b' Ω a d Λ (2*hatG O n (i+1) x) (rangeG O n (i+1) κ τ'.t x) (delay O n (i+1) x) τ'.t θ) (hm: ScoresU (k:=k) B (j+1) 0 T' a d Λ x b' Ω O κ τ'.t s)(hs:0<s) (hf:0<y)(hr:y≤ Fare.solar (hint O B k j T') Q.table (V i))(hv:0<v')(L L2 Z0 Z1 Z2:ℝ)(hμ:s=expo L (finC O B (j+1) k))(hη:θ=expo L2 (finC O B j k))(hΓ':v'=expo Z0 (finC O B j k))(hU':y=expo Z1 (finC O B j k))(hee: Z2= toga τ' o O Z1 (tallyK O.L x j))(hC:t*v'≤ (Cvol (A0 (i+1))).re): Real.exp ((bear O.L*L+L2-Z2-Z0)/leafZ N) ≤ Wv i:=by
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
    have hv': L₁≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> (Grass.price x.val).trans (by rw [one_mul]; exact le_rfl)) -- application inspect
    rw [hη,hμ,hΓ',show C₁=expo Z2 (finC O B j k) from ?_] at hε
    · have hx: g₁ ≤ expo (bear O.L*L+L2-Z2-Z0) (finC O B j k):=by
         rw [tour_c B] at hε; apply hε.trans; unfold expo; rw [mul_sub,mul_sub,mul_add,Real.exp_sub,Real.exp_sub,Real.exp_add] -- expo unfold
         -- direct algebra
         let Q1:= expo (bear O.L*L) (finC O B j k); let Q2:= expo L2 (finC O B j k); let P1:= expo Z0 (finC O B j k); let P2:= expo Z2 (finC O B j k)
         change L₁*(Q1*Q2)/(P2*P1) ≤ Q1*Q2/P2/P1; rw [div_div]; exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le hv') (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
      unfold g₁ at hx; rw [he₁, gain_p (inv_pos.mpr hw)] at hx; unfold expo at hx; rw [Real.exp_le_exp,Real.log_inv] at hx
      apply le_trans _ (Real.exp_log hw|>.le); apply Real.exp_monotone; apply (div_le_iff₀ (leafZ_pos b')).2; have hD:0<(Fintype.card (Site (finC O B j k)):ℝ):=Nat.cast_pos.mpr Fintype.card_pos; apply le_of_mul_le_mul_left _ hD; linarith only [hx]
    unfold C₁; rw [hee, hU']; exact goodness B _ hh'
end IV
end Rails
end YM.QCD.Acre
