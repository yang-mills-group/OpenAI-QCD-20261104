import YM.Talis.Ports
import YM.Lyre.Price
import YM.Talis.Billet
import YM.Talis.Peak
import YM.Differ.Humming
import YM.Bard.Reel
import YM.Magi.Band
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
variable {S:Flight j j}{K:KernelChoices}{hBP:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K hBP)}
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open Track Depot
namespace Talis
open MintV Suburb.Affair.Nimbus Counter
variable (L:Side)
local notation "EV"=> measureV L
local notation "τ"=>distV L
local notation "Bp"=>run L
/-!
 # Monetary compounding.E. arbitrary arcs on Plateau. Stamp prices all offsets.
 -/
open Finset Suburb.Melt.Lobby MassiveQCD
open LeaseV FlareV
variable {I:Type}[Fintype I]
local notation "FP" j:arg=> ratioCostV (A.spacing j) (clockQ P₀ A x j)
noncomputable def stipend (j:ℕ)(_:I):= ratioCostV (A.spacing j) (clockQ P₀ A x j)
local notation "qW"=>stipend P₀ A (x:=x) (I:=I)
local notation "U"=>gainV (qW)
variable (b:ℕ)(Jv:IntervalE P₀ A L x z b n) {M:ℕ} (hP:n-b ≤ distV L M z)
include Jv hP
lemma tillsV (w:ℕ)(hv:b ≤ i)(hs:j ≤ n)(hp:i ≤ j)(hQ:j-i ≤distV L w z) (hr:∀ i<τ M z,let y:=riseV L z i; (EV 3 z)⁻¹ ≤ ratioCostV L y ∧ ratioCostV L y ≤ 1) (g:I): (EV (3+w) z)⁻¹ ≤U i j g ∧ U i j g ≤1 :=by
    let D:=Ico i j; let W k:= FP k; let p:=EV 3 z; have hz:gainV (qW) i j g=∏ k∈D,W k:=rfl; have h(k:ℕ): k∈D→ p⁻¹ ≤ W k ∧ W k ≤1:=by
             intro hu; obtain ⟨hl,h'⟩:=mem_Ico.mp hu; let t:=hv.trans hl; let hq := h'.le.trans hs; rw [show W k=_ from (show W k= FP k from rfl), Jv.starts k t hq,Jv.spins k t hq]; exact hr (k-b) (by omega) -- syntax
    rw [hz]; have hh:D.card ≤ τ w z:= Nat.card_Ico i j|>.le.trans hQ -- args
    refine ⟨?_, ?_⟩
    · have ht:(∏ k∈D,p⁻¹) ≤ ∏ k∈D,W k:=prod_le_prod (fun k hi=> (inv_pos.mpr (χone L z 3)).le) (fun k hi=> (h k hi).1)
      rw [prod_const,_root_.inv_pow] at ht; refine (inv_anti₀ (pow_pos (χone L z 3) _) ?_).trans ht
      exact (pow_le_pow_right₀ (uniformV ..) hh).trans (nexE L 3 w z|>.le)
    apply le_trans (b:=∏ k∈D,(1:ℝ)); · exact prod_le_prod (fun k hi=> by change 0 ≤ W k; exact (inv_pos.mpr (χone L z 3)).le.trans (h k hi).1) (fun k hi=>(h k hi).2)
    simp
omit Jv hP
variable (a:ℕ)
-- choose exact boost at restore.NEW Lens path any.Demand eventual.
variable (j₁ n₁ h₁:ℕ)(C:ℝ→ℝ)
noncomputable def restore (i j:ℕ)(C:ℝ)(g:I) := C / (gainV (stipend P₀ A (x:=x)) i j g * Blessing.birthV L a z)
local notation "rp"=> restore P₀ A L a (C:=C)-- check arity
noncomputable def countCash (k:ℕ)(n:ℕ) := measureV L k z * (measureV L a z * measureV L (3+n) z)
local notation "Xq" i:arg j:arg b:arg=> restore P₀ A L a i j b (x:=x) (z:=z) (I:=I)
-- output bound in expression C any positive
include Jv hP
lemma witness (f u k:ℕ)(y:ℝ)(hy:0<y)(ht:y ≤ EV f z)(hp:b ≤ i)(hv:i≤j)(he:j ≤ n)(hd:j-i ≤distV L u z)(hK: countCash L a f u (z:=z) ≤ EV k z)(hr:∀ i<τ M z,let y:=riseV L z i; (EV 3 z)⁻¹ ≤ratioCostV L y ∧ ratioCostV L y ≤ 1)(p:I):
   let r:=restore P₀ A L a i j y p (x:=x) (z:=z); 0<r ∧ |r|≤ EV k z ∧ r * gainV (stipend P₀ A (x:=x)) i j p *Blessing.birthV L a z=y:=by
       intro r
       let u':=gainV (qW) i j p; let t:= Blessing.birthV L a z; let Z:=EV (3+u) z
       have hm:= (tillsV P₀ A L b Jv hP u hp he hv hd hr p).1 -- order check
       have hℳ:=χone L z (3+u); have hq:0<u':=(inv_pos.mpr hℳ).trans_le hm; have hQ:= Blessing.biotic L a z; have hA:0<t:= hQ.1; have hl:0<r:= div_pos hy (mul_pos hq hA)
       rw [abs_of_pos hl]; refine ⟨hl,le_trans ?_ hK,?_⟩; unfold countCash
       · calc
              r ≤ EV f z/(Z⁻¹*t):= div_le_div₀ (zero_le_one.trans (uniformV ..)) ht (mul_pos (inv_pos.mpr hℳ) hA) (mul_le_mul_of_nonneg_right hm hA.le)
              _ = _:=by unfold t Blessing.birthV Z; simp [div_eq_mul_inv,mul_comm]
       change y/(u'*t)*u'*t = _; field_simp
omit Jv hP
lemma canDive {w a' f:ℕ}(ht:a<a')(hr:3+w<a')(hf:f<a')(hL:1<L.val): ∀ᶠ z in atTop,countCash L a f w (z:=z) ≤ EV a' z:=by
    let p:=max (3+w) (max a f); have hp:p < a':= max_lt hr (max_lt ht hf); have hh(a:ℕ)(ha:a ≤ p) : PageP L (measureV L a) p := PageP.budget_lo L ha
    apply PageP.cheaper L (A:=p) _ hL hp; exact (hh f (by unfold p; omega)).times L ((hh a (by unfold p; omega)).times L (hh (3+w) (by unfold p; omega)))
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.witness
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.canDive
