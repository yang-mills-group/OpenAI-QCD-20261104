import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
import YM.QCD.Grove.Sphere
/-! # Oars accounting; sewn analytic collection first. Consume when actual V Healthy
 (boundary ANY). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F L:Side} {j i m n W w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side} {q : ℝ}
section morph
variable {q q' : Stars→ℝ} (Q:∀ i:Stars,(Y i).val=2*(w*roller i.val)) (z:ℕ) (fa: ∀ i:Stars,Offer G (Y i))
lemma spruce (x:Site c): mist Q (rip fa) x=∑ j:Stars, glimmer w j • ((Boulevard.stillA (Trio.froth (fa j))) ∘ Slide.shape (Trio.trackR Q j) x):= by
  funext i; simp only [mist,rip,unitR,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,froth,Boulevard.stillA,sum_sub_distrib]
-- pay oath from prior erudition ON points very small.
def oroH (w:ℕ) (B:BudgetPoint) (z:ℕ) (q : Stars→ℝ) := ∑ i : Stars, |Slide.glimmer w i| *(tilt B z*q i)
variable (h : ∀ i j, B.Regular univ (fa i j)) (hq : ∀ i,0≤q i) (hp:81*w ≤ z)
include h hp hq
lemma tallR (e a : ℝ) (x:Site c)
    (he:∀ V: Config G c, Healthy B.threshold (neighbors z x) V→ ∀ i, ∃ (u:Site (Y i)→G.El) (P:Positions (Uniform.Primary (Y i) G)), actual P= gauge u (Slide.shape (trackR Q i) x V)∧ ‖P‖+2*e <a)
    (hM: ∀ i (P : Positions (Uniform.Primary (Y i) G)),flags B.threshold (actual P)=∅→ ‖P‖+2*e < a → ∀ l: List (Directions G (Y i)),l.length ≤B.order→ (∀ i∈l, ‖i‖≤ B.threshold)→ ‖leftDerivs (Boulevard.stillA (Trio.froth (fa i))) l (actual P)‖ ≤ q i) :
    B.supBounds x (neighbors z x) (mist Q (rip fa) x) (oroH w B z q):= by
  rw [spruce]; let p i:= Boulevard.stillA (Trio.froth (fa i))
  have hh i:B.Regular univ (p i):= by
    have hx : B.Regular univ (froth (fa i)):= by rw [show froth (fa i)=∑ j,fa i j from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _=> h i j
    exact CouplingShape.reg_sub hx (CouplingShape.reg_const _)
  have hz i (j:Site (Y i)): separation x (Slide.sites (trackR Q i) x j)≤z:= (Slide.village (C:=Y i) (w:=w*roller i.val) (Q i).ge _ _).trans (by exact (roll_cap w i).trans hp)
  apply sup_S (B:=B) _ _ _ _ _ (fun i _=>CouplingShape.reg_scale _ (Slide.regular (trackR Q i) x (hh i) fun j=> (neighbors_mem ..).2 (hz i j)))
  intro i _; apply CouplingShape.sup_scale _
  refine ⟨mul_nonneg (by unfold tilt; positivity) (hq i),fun V hu l hl hd=>?_⟩
  obtain ⟨u,P,hP,hR⟩:= he V hu i; let W:=Slide.shape (trackR Q i) x V; have hK := Trio.hintQ Q z V i hp x hu
  apply Slide.stalled (trackR Q i) x (p i) (hz i) l V hl hd ((hh i).smooth _ (by unfold Healthy; rw [hK]; simp))
  have hf:= hM i P (by rw [hP, gauge_flags,hK]) hR; rw [hP] at hf; exact Slide.bills u (hh i).symmetry hf
end morph
end YM.PhysicalNext.Repeat.Trio
