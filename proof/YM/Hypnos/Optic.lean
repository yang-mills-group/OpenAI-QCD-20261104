import YM.Hypnos.Knell
import YM.VStages.Through
import YM.Massive.Beacon.Keys
/-! # Cost settlement of actual w on staircase from width at L and
physical real Leg normalization. Applies to true selected Tally, even
when β^head measured separately. Puiseux expense after perturbative purchases. -/
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
variable {c f C F L:Side} {J:Patch} {j k k₀ n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j k₀}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
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
namespace Cairn
open LicenseM
open Finset Grass NormedSpace MeasureTheory High PrismT
open Lunar Ring0 Stew.Project Sq
variable {s Θ W' u₀ v₀ tol α3 ν' σ η':ℝ}{χ:Chi}{R₀:ParcelR}{U V:SunR R₀}{τ:Policy Q T'.below N}
variable (P₀:Plan j)(P₂:Plan k₀)
set_option quotPrecheck false
local notation "λ₀"=> run S.L x
local notation "Tq"=> T'.top.clip
local notation "D₀"=> FieldB R₀ V c (haloK S.L x) P₂ S.land
local notation "δ'"=> A+(N:ℝ)*γ
variable {β b v Λ κ A3 H':ℝ}{Δ:PlaqAxes}
variable (F₀:Flavor N)(X:Voice f N)(Z:Gem c N (LayerQ c)) (B: Manifest P₀ P₂ τ R P o χ T U b (run S.L x) (1/8) β μ z)
local notation "X!"=> red X.P X.K U P₀ S.wing R T.up T'.top.clip (haloK S.L λ₀) β b 0
local notation "u'"=> roofK S.L τ.t κ x

private lemma racer_aux {v:ℝ} (hv:0<v)(u:ℝ) (hu:|v^2-1| ≤ u):|v-1|≤u:=by
    have hs:=mul_le_mul_of_nonneg_left (show 1 ≤ |v+1| from (le_add_of_nonneg_left hv.le).trans (le_abs_self _)) (abs_nonneg (v-1))
    rw [mul_one,← abs_mul] at hs; refine hs.trans ?_; rw [show (v-1)*(v+1)=v^2-1 by ring]; exact hu
-- fixed L.budget. Agree under Order.L
abbrev turfP (X:ℝ)(L:Side)(y:ℝ)(N:ℕ) := (hauteur N).choose*(X*Jets.Touch.chip L y)
structure LitG (L:Side)(η x ξ:ℝ)(p:BudgetPoint)(c:Side)(b:Flavor N):Prop where
   license : ∀ D: Voice c N, Glory L p b η x 1 D → |unitF true c (Stew.meter b (Patron.total D.P p.threshold 1))|≤ ξ
lemma liftG (L:Side)(η x ξ:ℝ)(p:BudgetPoint)(b:Flavor N)(hξ:0<ξ)(he:p.supportExponent=2):∀ᶠ c:Side in atTop, LitG L η x ξ p c b:=by
    filter_upwards [chargeQ b true p (Jets.Touch.chip L x) (fan_pos L η x), (flash_top p.B).eventually_le_const hξ] with c hx h
    exact ⟨fun D hD=> (hx D.ι D.P (he ▸ hD.portraitP.quoteE) hD.portraitP.passE hD.portraitP.pure1).trans h⟩
variable {ε β' m':ℝ}
set_option maxHeartbeats 910000 in
lemma pacing (hp: Knells P₀ P₂ τ B Z V F₀ A γ Λ α3 ν' κ tol A3)
    (ht:0<s)(hH:T.high=Tq)(hX:Enn R F₀ S.L λ₀ τ.t (1/8) (duo X.P X.K))(hb: |β+δ'|+1≤W')(hm:EveningR c P T.down T'.below.clip S.L x τ.t Λ W' F₀ Δ u' u₀ v₀ H' tol) (hs:1 ≤ speedP S.L τ.t x)(he:LitG S.L τ.t x ε P c F₀) (Hw:0<w)(hY: NormG D₀ F₀ (vest c N w (fortQ S K h N β (s • (X!)))) P T.down T'.below.clip V.Z.page Δ u₀ v₀ H' β' m') : |w-1| ≤ 16*turfP α3 S.L x N+16*ε :=by
  obtain ⟨p,Γ,-,-,-,-,-,-,⟨K₀⟩⟩:=hp.ride X.ι X.β (duo X.P X.K) hX
  let G:=K₀.toSparkW.toPaymentM
  let t:= G.pQ
  letI:= G.cnt
  let F:=Classical.choice (Tree.select (S.visit K h).ratio S.odd)
  let d:= Collection.vac (Reggae.stock (charm G.R4 Z F₀)) (perfume c (PhysicalNext.Repeat.Song.weighty B.Pq χ F) t)
  let D':= gleams T P₀ P₂ X F₀ B Z G; let m':= mCoeff G.R4 Z F₀; let a:=powerU G.R4 Z F₀; let r':=betaP G.R4 Z F₀
  let U':= park S h P₀ U.X U.Y (haloK S.L λ₀) b; let R':=Real.exp (Real.log (U' 1).det.re)^N*pot c d
  obtain ⟨hG,ha,ha2,hr,hF,hm',hu,hR,hJ⟩:= relu T P₀ P₂ X F₀ B Z G hH F
  have ht':|β+δ'+r'|≤ W':= ((abs_add_le ..).trans (add_le_add_right hr _)).trans hb
  obtain ⟨D₁,M₁,W₁,p₁,hP,hM,hW,hA,hν,hc,hΩ,hZ,hz,hN⟩:= hm.immigrates D' D₀ ⟨Z,hu⟩ hG (β+δ'+r') m' V.Z.page hm' ht'
  let FV:=bio P D' T.down T'.below.clip D₀ V.Z.page (β+δ'+r') m'; let GV:=bio P D₁ T.down T'.below.clip D₀ V.Z.page (β+δ'+r'+p₁) M₁
  obtain ⟨h1,h2⟩:=canonXQ a W₁ s R' ha hν (X!) FV GV (funext hZ) hJ
  have hy : NormG D₀ F₀ (vest c N (W₁*a) (fortQ S K h N β (s • (X!)))) P T.down T'.below.clip V.Z.page Δ u₀ v₀ H' (β+(δ')+r'+p₁) M₁:=by rw [h1]; exact oasisP F₀ hN (mul_pos ht hR)
  rw [(same_keys hY hy hz hm.gift Hw (mul_pos hν ha)).1]
  -- licence1 supplies infinitesimal. leg ratio.
  let Pj:= turfP α3 S.L x N
  have hx': |qWave (till G.R4 F₀ 0)| ≤ Pj:= (le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hs)).trans (((hauteur N).choose_spec).2 c G.I₁ G.R4 P _ _ (speedP S.L τ.t x) K₀.lis (zero_lt_one.trans_le hs) (by have h:= T'.below.price_pos; linarith) F₀).2
  have hθ: |legϑ G.R4 Z F₀|≤ 2 * Pj:=by unfold legϑ; rw [abs_div]; have hm:=hu.earn F₀; let p:=qWave (till Z F₀ 0); change 1/2≤ p at hm; change _/|p|≤_; rw [abs_of_nonneg (by linarith : 0≤p),div_le_iff₀ (by linarith)]; nlinarith only [hx',abs_nonneg (qWave (till G.R4 F₀ 0)),mul_le_mul_of_nonneg_left hm ((abs_nonneg _).trans hx')]
  have hA0: |a-1| ≤ 8*Pj:=by
       let z:=legϑ G.R4 Z F₀; have hx : 0<1+z:=Real.sqrt_pos.mp (inv_pos.mp (show 0 < (Real.sqrt (1+z))⁻¹ from ha)); have ha' : a^2*(1+z)=1:=by unfold a powerU; change (Real.sqrt (1+z))⁻¹^2*_=_; rw [inv_pow,Real.sq_sqrt hx.le,inv_mul_cancel₀ hx.ne']
       apply racer_aux ha; rw [show a^2-1=z*-(a^2) by linarith only [ha'], abs_mul, abs_neg, abs_of_nonneg (sq_nonneg a)]; calc
          _ ≤ 2*Pj*4:= mul_le_mul hθ (by nlinarith only [ha,ha2]) (sq_nonneg _) ((abs_nonneg z).trans hθ)
          _ = _ := by ring
  -- compare W1 at physical torus. q unit parity.APA
  let H:= unitF true c (D₀ 1); let M':= unitF true c (Stew.meter F₀ (Patron.total D'.P P.threshold 1)); have hMv:|M'| ≤ ε:=he.license D' hG
  have heq : W₁^2*(H+M')=H:=by
        have hr : tollM true F₀ (GV 1)=W₁^2*(H+M') := by
            rw [show GV 1=_ from (hZ 1).symm, toll_earn]; unfold bio; rw [PrismT.spoke, if_pos rfl, add_zero]
        rw [←hr]; exact hN.lea
  change 1/4≤H at hz
  have hB1 : |W₁-1|≤16*ε:= racer_aux hν _ (by
     apply le_of_mul_le_mul_right _ (by linarith : 0<H); rw [show |W₁^2-1| *H=|(W₁^2-1)*H| by rw [abs_mul,abs_of_pos (by linarith only [hz] : 0<H)],show (W₁^2-1)*H = -(W₁^2*M') by linarith only [heq], abs_neg,abs_mul,abs_of_nonneg (sq_nonneg W₁)]; nlinarith only [mul_le_mul (show W₁^2≤4 by nlinarith only [hν,hc]) hMv (abs_nonneg _) (by norm_num),mul_le_mul_of_nonneg_right hz ((abs_nonneg _).trans hMv)])
  rw [show W₁*a-1=W₁*(a-1)+(W₁-1) by ring]; refine (abs_add_le ..).trans (add_le_add ?_ hB1); rw [abs_mul,abs_of_pos hν]; exact (mul_le_mul hc hA0 (abs_nonneg _) (by norm_num)).trans_eq (by unfold Pj; ring)
end Cairn
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Cairn.pacing
