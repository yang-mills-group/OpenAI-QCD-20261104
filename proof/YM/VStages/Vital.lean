import YM.VStages.Haven
import YM.VStages.Hometime
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
namespace Affair
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Calm P₀ A X x)
local notation "OC"=> fun i=>A.ring (B.n k) i
lemma epilog (i k:ℕ) (M:Voice (A.ring (B.n k) i) N)(α t₀:ℝ):
   Zest P₀ A X B T Pt i k M α t₀= quoteF _ M (J (A.level i)) (T.W.state i).wing (P.stage (A.level i)).clip (T.W.state i).path (Pt i) (closing P₀ A X B T i) (haloK (A.spacing i) (clockQ P₀ A x i)) α t₀:=by
   rw [Spire.curtain (terminal P₀ A i x)]; rfl

local notation "Lₜ"=> A.spacing i
local notation "λₜ"=> clockQ P₀ A x i
local notation "Cₜ"=> A.ring (B.n k) i
local notation "Ptq"=> (J (A.level i))
abbrev Pricing (L:HaarBudget su) (O:Paved P₀ A X x) (i k:ℕ)(Y:Pixel (A.ring (B.n k) i) N)(z:ℝ):=
   NormPrices L (twist (P:=P) (A.node i)) (gaugeSize (A.spacing i) (clockQ P₀ A x i)) (O.M i) (O.Y i) Y z
lemma fundsV (h: |α| ≤ MassBox P₀ A x i) (hc:Calm P₀ A X x): |α| ≤ roofK (A.spacing i) θ (halo₀ P₀ (A.spacing i) (A.node i)) (clockQ P₀ A x i):=by
   let L:= A.spacing i; let K:= valueK P₀ A i; let u:=clockQ P₀ A x i
   have hm:0 < roofK L θ K u := (hc.pool i).warms.pos
   have ht:= ceilingW P₀ A hc.growth (hc.kind i).warms.pos.le
   apply h.trans (ht.trans _); change ((L.val:ℝ)/128-1)*roofK L θ K u ≤ roofK L θ ((L.val:ℝ)/128*K) u; rw [show roofK L θ ((L.val:ℝ)/128*K) u=L.val/128*roofK L θ K u from by unfold roofK Emax; ring]; linarith only [hm]
variable (Lb:HaarBudget su) (O:Paved P₀ A X x) (ho:Campus P₀ A X O B k n)
include hp hc
lemma rich_mass (hi:i≤n): |U i|≤1:= (hp.window i hi).2.2.2.1.trans (hc.kind i).upper
include ho hX
set_option maxHeartbeats 700000 in
lemma reachesT (hi:i ≤ n)(hN:Even N):∃ (Y:Voice (A.ring (B.n k) i) N) (z:ℝ),
      Enn (Pt i) F₀ (A.spacing i) (clockQ P₀ A x i) θ (1/8) (duo Y.P Y.K) ∧ 0<z ∧
      F i=z • Zest P₀ A X B T Pt i k Y (V i) (U i) ∧ Pricing P₀ A X B Lb O i k (F i) z:=by
   let n':= Cₜ; let β:=V i; let Q0:= Pt i; let q:=gaugeSize Lₜ λₜ
   have hU:= hp.window i hi
   let Y':= closing P₀ A X B T i; let σ:= clockQ P₀ A x i; let u:= run Lₜ σ
   obtain ⟨M,z,hz,hM,hh⟩:= hU.2.2.2.2
   let S:= T.W.state i
   have hM':= Spire.germSet (terminal P₀ A i x).symm F₀ M hM
   have hg:1 ≤ β:= hU.2.2.1; have hb: β≤2*u:=by unfold u σ; rw [augmented]; exact hU.2.1.2
   have ht:u/2≤ β:=by unfold u σ; rw [augmented]; exact hU.2.1.1
   have hu:= fundsV P₀ A X hU.2.2.2.1 hc; have hx:=waking P₀ A (hX i)
   obtain ⟨h1,h2,h3⟩:= realpath P₀ A X B T Z V U W F hp hX hc hN i hi; obtain ⟨C₀,l,hc0,h0⟩:= ho.2.2 i hi; let s:=h0
   have heq: F i=z • Rails.red M.P M.K Y' (Ptq) S.wing Q0 S.path TZ (haloK Lₜ σ) β (U i) 0:=by
       rw [hh]; rw [epilog]
   have hS:(S.path).Bounds TZ (P.stage (A.level i)).width (P.allowance (A.level i)) (stanceQ P₀ A i):= (Spire.Client.Terrace.stays S.priced (le_max_right ..)).1
   have he:4≤ (Cₜ).val:= ho.1.trans (orbitTall P₀ A _ _) -- notation.C
   have hv:0 < q:= h0.g_pos
   have hz₀:u*q^2=1:= h0.exact_
   refine ⟨M,z,hM',hz,hh, NormPrices.byRoots Lb _ _ _ (by omega) hz.le hv ?_ h1 ?_⟩
   swap
   · intro x; rw [show F i x=z • _ from congr_fun heq x,norm_smul,Real.norm_of_nonneg hz.le]; exact mul_le_mul_of_nonneg_left (h0.high n' Q0 hx M hM' S.wing Y' S.path β (U i) hS hu ht hb x) hz.le
   let W₁:=Lb.small*q^su.lieDim; let D0:=Real.exp (-(K.penalty*2)); have hΛ: 0 ≤ W₁:= mul_nonneg Lb.positive.le (by positivity); have hD:0≤ W₁*D0:=mul_nonneg hΛ (Real.exp_pos _).le
   by_cases h:i=n
   · -- avoid subst N. rewrite in hp.bare via generalization
     have heven : Even (A.ring (B.n k) i).val:= orbitEven P₀ A _ _ ho.2.1
     have hE: β*q^2 ≤ 2:= by linarith only [mul_le_mul_of_nonneg_right hb (sq_nonneg q),hz₀]
     have hzq:∀ U',Cove.light _ (F i U')=primalD n' N β (U i) U':=by
          subst i; exact soul P₀ A X B T Z V U W F hp hX hc
     apply le_trans _ (size_start (J:=(A.flight i).patch) (Ptq) F₀ Lb q hv h0.g_le (zero_le_one.trans hg) hE heven he _ M h0.fan_ hM' h0.chip hx.ball Y' _ _ _ _ (U i) z (rich_mass P₀ A X B T Z V U W F hp hc hi) hz heq hzq)
     · exact mul_le_mul (mul_le_mul_of_nonneg_left (Globe.earns h0.cap) hz.le) (pow_le_pow_left₀ hD (mul_le_of_le_one_right hΛ (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg K.penalty_pos.le zero_le_two)))) _) (pow_nonneg hD _) (by unfold Globe.expo; positivity)
   · have hn:i<n:= lt_of_le_of_ne hi h
     have hG:= hp.window (i+1) hn; let x':= V (i+1); have hz':z*Globe.expo (O.Y i) n' ≤ (cBer (F i) 1).re:= h0.low _ Q0 M hM' S.wing Y' S.path β (U i) hu _ hc0 z _ hz heq h2
     have hv': x'*q^2≤4:=by
         have hh:x'≤2*run Lₜ u:=by simp only [u,σ, augmented,← engaged P₀]; exact hG.2.1.2
         have he: x' ≤ 4*u:=by linarith only [hh,(show run Lₜ u ≤ 2*u from h0.adjacent)]
         linarith only [hz₀,mul_le_mul_of_nonneg_right he (sq_nonneg q)]
     let X':= (stepper P₀ A X B T i).visit Kz (A.next (B.n k) i)
     have hq:X'.kernel=K:=rfl
     apply le_trans _ (minorR P₀ A X B T Z V U W F hp hX hc i hn hN (by omega)); rw [mul_comm]
     exact mul_le_mul (pow_le_pow_left₀ hD (noiseZ Lb X' hv h0.g_le (zero_le_one.trans hG.2.2.1) hv') _) hz' (mul_pos hz (Real.exp_pos _)).le (pow_pos (StepData.penaltyZ_pos ..) _).le
include Lb
lemma meaningful (hN:Even N)(i:ℕ)(h:i≤n):0 < (Cvol (F i)).re:=by
   let U':= clockQ P₀ A x i; obtain ⟨Y,z,hψ,h₀,he,hh⟩:= reachesT P₀ A X B T Z V U W F hp hX hc Lb O ho h hN -- U shadow!
   obtain ⟨c,k,hf,hg⟩:= ho.2.2 i h
   apply lt_of_lt_of_le _ hh.lower
   have hA:= Lb.positive; have hB: 0 < gaugeSize (A.spacing i) (clockQ P₀ A x i):= hg.g_pos; unfold Globe.expo; positivity
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.reachesT
