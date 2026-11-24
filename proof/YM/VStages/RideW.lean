import YM.VStages.WeatherW
import YM.Massive.Reference.Prototype
import YM.VStages.Vital
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
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
-- genuine physical schema.Aff.
def ladder : Scheme where
    choices:=K
    J:=fun i=>rank (A.level i)
    step:= Track.flight A
    admissible i:= (A.ticket i).owns
lemma ladders (m:ℕ): (ladder P₀ A).ratio m= A.den m:=by
    induction m with
    | zero=>rfl
    | succ i ih=> rw [Massive.Scheme.ratio,ih, Track.den]; rfl
lemma rungs (B m):(ladder P₀ A).side B m=A.ring B m:=by unfold Massive.Scheme.side Track.ring; rw [ladders]
lemma ladder_cost (i:ℕ): Real.log (((ladder P₀ A).spacing i)⁻¹)=A.measure i:=by rw [Massive.Scheme.spacing,ladders, _root_.inv_inv]; rfl
lemma ladder_time : Tendsto (ladder P₀ A).spacing atTop (𝓝[>] 0):=by
    have he(i):0<(ladder P₀ A).spacing i:=by unfold Massive.Scheme.spacing; positivity
    have hp: Tendsto (fun i=> ((ladder P₀ A).spacing i)⁻¹) atTop atTop:=by
       apply (Real.tendsto_exp_atTop.comp A.long).congr'; filter_upwards with i; rw [Function.comp_apply, ← ladder_cost,Real.exp_log (inv_pos.mpr (he i))]
    exact tendsto_nhdsWithin_iff.mpr ⟨by convert tendsto_inv_atTop_zero.comp hp using 1; ext; simp, Eventually.of_forall (fun i=>he i)⟩
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
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open YM.Massive.Reading (planeProbe)
local notation "Lₜ"=> A.spacing i
local notation "λₜ"=> clockQ P₀ A x i
local notation "Cₜ"=> A.ring (B.n k) i
local notation "Ptq"=> (J (A.level i))
-- β and w & coherent orientation. Notation caution
abbrev march_R (n k:ℕ): Massive.Run (ladder P₀ A) n (B.n k) N:=Massive.Scheme.run _ _ V W (fun _=>U n) n
include hp hX hc
omit hX in
lemma balanced (he:4≤ (B.n k).val)(ht:Even (B.n k).val): (march_R P₀ A B V U W n k).Actual:=by
   have hQ: |U n| ≤1:= rich_mass P₀ A X B T Z V U W F hp hc le_rfl
   exact Massive.Scheme.strict _ _ _ _ (u:=fun _=>U n) (fun i hi=> zero_lt_one.trans_le (hp.window i hi).2.2.1) (fun i hi=>(hp.relay i hi).real) ht he (fun i=>show U n+4 ≠0 from ne_of_gt (by linarith only [(abs_le.mp hQ).1]))
omit hp hX hc in
private lemma physicalQ (S:Flight j k) (V:Train j)(K:KernelChoices)(h:f.val=c.val*S.L.val)(V':Pixel f N)(U:Pixel c N) (w α:ℝ)(hw:0 < w) (hV:∀ x, advanceF (helm S V) K h V' α x=gBody c w (U x)): transfer S K h α w (Cove.light _ ∘ V')=Cove.light _ ∘ U:=by
  funext p; change Massive.rescale w (advanceF (helm S V) K h V' α p)=_; rw [hV]; change (Cove.light _ (wearK c N w (wearK c N w⁻¹ (U p))))=_; rw [wit _ w w⁻¹ (mul_inv_cancel₀ hw.ne')]; rfl
set_option maxHeartbeats 620000 in
theorem exact_T (i:ℕ)(he:i≤n): (march_R P₀ A B V U W n k).density i= transit (rungs P₀ A _ _).symm (Cove.light _ ∘ F i):=by -- rungs orientation flips
   let S:= ladder P₀ A; let V':= S.run (B.n k) V W (fun _:Flavor N=> U n) n; let Y:= S.wilson (B.n k) V (fun _:Flavor N=> U n) n
   induction he using Nat.decreasingInduction with
   | self=>
       have he : V'.density n= ⇑Y.density:=by change ⇑(S.toStop (B.n k) V W n n Y.density)=_; rw [Massive.Scheme.entrance]; rfl
       change V'.density _ =_; rw [he]; unfold Y; rw [show (Cove.light _ ∘ F n)= primalD (A.ring (B.n k) n) N (V n) (U n) from funext (soul P₀ A X B T Z V U W F hp hX hc)];
       suffices M:∀ f:Side,∀ (h:A.ring (B.n k) n=f), ((⟨V n,0,fun _=>U n⟩:Regulator f N).density).toFun=transit h (primalD _ N (V n) (U n)) by exact M _ _
       intro f h; subst f; rfl
   | of_succ i hi ih=>
       have hv:=hp.relay i hi
       have hh : (march_R P₀ A B V U W n k).density i= transfer (A.flight i) K _ (V (i+1)) (W i) ((march_R P₀ A B V U W n k).density (i+1)):= Massive.Run.Carried.eqn (S.carried (B.n k) _ _ Y.density (fun _=> U n)) (m:=i) (by omega) hi
       rw [hh,ih]; suffices H:∀ f c:Side,∀ (h:f.val=c.val*(A.spacing i).val)(hF:A.ring (B.n k) (i+1)=f)(hC:A.ring (B.n k) i=c), transfer (A.flight i) K h (V (i+1)) (W i) (transit hF (Cove.light _ ∘ F (i+1)))= transit hC (Cove.light _ ∘ F i) by exact H _ _ _ _ _
       intro f c h hF hC; subst f c; exact physicalQ _ (T.W.state (i+1)).wing _ _ _ _ _ _ hv.real hv.body

variable {ε:ℝ}{O:Paved P₀ A X x}
variable (ho:Campus P₀ A X O B k n)
include O ho
lemma ridePrice (L:HaarBudget su)(i:ℕ)(hN:Even N)(hi:i ≤n)
    (hh:Envelope (x:=x) P₀ A B Pt k i ε):
       let R:=march_R P₀ A B V U W n k; Massive.Stiffness.Window (R.density i) (R.β i) ε ∧ (i<n→∀ f:Flavor N,‖R.massRead i f-(U i:ℂ)‖≤ ε):=by
       obtain ⟨h,hG⟩:= proves P₀ A X B T Z V U W F hp hX hc L O ho hh hi hN
       have he:= exact_T P₀ A X B T Z V U W F hp hX hc i hi
       intro Y; change Y.density i=_ at he
       constructor
       · rw [he]; exact Reference.crossW _ h
       intro hi f; change ‖planeProbe (Y.density i) f-_‖≤_; rw [he,crossP]; exact hG hi f
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.ridePrice
