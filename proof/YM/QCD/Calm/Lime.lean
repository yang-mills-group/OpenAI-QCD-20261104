import YM.QCD.Calm.Manna
/-! # Books and Schema combination, common χ. FOREST amount high separate on real lease only.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Calm
open Function Filter Metric MeasureTheory Lattice Wilson Pressure Pressure.Testing RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.L2Operator
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR Birth Beam
open GasP Ursell Greenbelt Patron Fount Oasis Stem Grove Slide Trio.Sharp Stew Creek
open Animals AnalyticBridge.VerifiedReset Deck
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame Deck Meadow
open Brick Dust Grove Moss Gas Blaze King Shells
open scoped PhysicalNext.Repeat.Greenbelt
variable {p a t u D A θ h b' M h' ξ ζ w w' r μ δ β k' W z v : ℝ}{I J V: Type}{m b s q N n j l :ℕ}{L c C f:Side}{B:BudgetPoint}
open Box Entr YM.Next.Scheduling AnalyticBridge VerifiedReset Song Meadow Quotes Time
-- Lymn full. need spend many space. Joint Linear accommodation.
variable {P Q Y V' A' K:Payday}
abbrev vasta (W U F M S T:Box c N)(m:ℝ):Box c N:= joins (joins W (joins U F)) (joins (buys M (-m)) (joins (buys S (-1)) (buys T (-1)))) -- matches barP. P' high prop
variable (W₀ U F D' S T:Box c N)
lemma seedN (h:0 ≤ V')(hp:0 ≤ A')(he:0 ≤ K)(hz:‖p‖ ≤1): P+(Q+Y)+(pom (-p) V'+(pom (-1) A'+pom (-1) K)) ≤ P+(Q+Y)+(V'+(A'+K)):=by
    have hp': ‖- (1:ℝ)‖ ≤1:=by rw [norm_neg,norm_one]
    exact Payday.stax Payday.idem (Payday.stax (Payday.saturate h Payday.idem (by rw [norm_neg]; exact hz)) (Payday.stax (Payday.saturate hp Payday.idem hp') (Payday.saturate he Payday.idem hp')))
lemma earsL (hP:Earn W₀ B n t a r P)(hQ: Earn U B n t a r Q)(hY:Earn F B n t a r Y)(hV:Earn D' B n t a r V')(hA:Earn S B n t a r A')(hK:Earn T B n t a r K)(ht:1 ≤ t)(hr:0≤r)(ha:0≤ a)(hp:‖b'‖≤1): Earn (Calm.vasta W₀ U F D' S T b') B n t a r (P+(Q+Y)+(V'+(A'+K))):=by
    have he:=zero_lt_one.trans_le ht
    have h:= Box.stores _ _ (Box.stores _ _ hP (Box.stores _ _ hQ hY ht ha hr) ht ha hr) (Box.stores _ _ (scaled _ hV ht ha hr (-b')) (Box.stores _ _ (scaled _ hA ht ha hr (-1)) (scaled _ hK ht ha hr (-1)) ht ha hr) ht ha hr) ht ha hr
    exact Payday.sit _ h (seedN (Payday.positive_pay _ hV he) (Payday.positive_pay _ hA he) (Payday.positive_pay _ hK he) hp)
lemma frames {w' q' m':ℕ} (W X G M A J: Box C N)(u:C.val=c.val*m)(g: Site C→ℂ)(hP:Acts W₀ W u g B n)(hQ:Acts U X u g B q)(hY:Acts F G u g B s)(hV:Acts D' M u g B l)(hA:Acts S A u g B w')(hT:Acts T J u g B q') : Acts (Calm.vasta W₀ U F D' S T b') (Calm.vasta W X G M A J b') u g B m' :=by
    unfold Calm.vasta; exact heals _ _ _ _ _ _ (heals (n:=0) _ _ _ _ _ _ hP (heals (n:=0) _ _ _ _ _ _ hQ hY)) (heals (n:=0) _ _ _ _ _ _ (Box.rings (n:=0) _ _ _ _ hV _) (heals (n:=0) _ _ _ _ _ _ (Box.rings (n:=0) _ _ _ _ hA _) (Box.rings (n:=0) _ _ _ _ hT _)))
end YM.QCD.Calm
