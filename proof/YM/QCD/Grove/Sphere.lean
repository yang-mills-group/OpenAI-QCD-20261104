import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Card
import YM.QCD.Grove.Count
/-! # Exact balance between Anchored charges Hp and loc mist of auxiliary views.
    All V. Orthogonality gives vanishing discrepancy on unpolluted. No Local purchase needed for α. -/
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
variable {G : Gauge} {c f C' F:Side} {j i m n W w r k l h:ℕ} {B : BudgetPoint} {Y:Stars→Side}
variable (Q:∀ i:Stars,(Y i).val=2*(w*roller i.val))
abbrev trackR (i : Stars) : Track (Y i):= Slide.cognac (Q i).ge
def voyageL (i : Stars) (x:Site (Y i)) (o:Site c) := o-wrap c (Slide.stage (trackR Q i) x)
variable (z: ℕ) (fa:∀ i:Stars,Offer G (Y i)) (V:Config G c)
-- REQUIRE z≥81*w so halos cover all journeys and then k≥z+(81*w)
lemma swayR (i:Stars) (x:Site (Y i)) (o:Site c): separation o (voyageL Q i x o) ≤ w*roller i.val:= by
  let u:=voyageL Q i x o; rw [separation_comm]; have he:= Slide.village (C:=Y i) (w:=w*roller i.val) (Q i).ge u x
  have hv:Slide.sites (trackR Q i) u x=o:= by unfold Slide.sites u voyageL; abel
  change separation u o≤_; rw [← hv]; exact he
lemma parcelH (hp:81*w≤z) (i:Stars) (x:Site (Y i)) (o:Site c) (h:2*z≤k): neighbors z (voyageL Q i x o)⊆ neighbors k o:= by
  let u:= voyageL Q i x o
  intro j hj; apply (neighbors_mem ..).2; have hv:= (neighbors_mem ..).1 hj
  apply le_trans (separation_triangle o u _); have ht:= swayR Q i x o; change separation o u≤_ at ht; change separation u j≤_ at hv; have hi:= roll_cap w i; omega
lemma hintQ (i:Stars) (hp:81*w≤z) (o:Site c) (h:Healthy B.threshold (neighbors z o) V): flags B.threshold (Slide.shape (trackR Q i) o V) =∅ := by
  apply allFlag _ _ _ _ _ _ B.threshold_pos.le h; intro x; apply (neighbors_mem ..).2; apply (Slide.village _ _ x).trans
  have hh:= (Q i); have hx : i.val ≤ 4:= by have ht:=i.isLt; omega
  exact (roll_cap w i).trans hp

variable (B)
def unitR (i: Stars) (x:Site (Y i)) (o:Site c) (V:Config G c): ℝ:= fa i x (Slide.shape (trackR Q i) o V)
def mist (o:Site c) (V:Config G c):= ∑ i:Stars,Slide.glimmer w i*∑ x:Site (Y i),unitR Q fa i x o V
def unearthed (o:Site c) (V:Config G c):= ∑ i:Stars, Slide.glimmer w i*∑ x: Site (Y i),
    let s:=voyageL Q i x o; masked B.threshold (neighbors z s) (unitR Q fa i x s) V

lemma sheens : ∑ i : Site c, masked B.threshold (neighbors z i) (mist Q fa i) V= ∑ i:Site c, unearthed B Q z fa i V:= by
  have ht i: masked B.threshold (neighbors z i) (mist Q fa i) V=∑ j: Stars,Slide.glimmer w j *∑ x:Site (Y j),masked B.threshold (neighbors z i) (unitR Q fa j x i) V:= by
    by_cases he:Healthy B.threshold (neighbors z i) V; · simp [masked_eq,he,mist]
    simp [masked_ne,he] -- formatting
  unfold unearthed; simp_rw [ht]; rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
  apply sum_congr rfl; intro i _
  rw [← mul_sum,← mul_sum]; apply congr_arg; rw [sum_comm]; conv_rhs => rw [sum_comm]
  apply sum_congr rfl; intro y _
  symm; exact Equiv.sum_comp (Equiv.subRight (wrap c (Slide.stage (trackR Q i) y))) (fun o=> masked B.threshold (neighbors z o) (unitR Q fa i y o) V)

-- Pointwise cancellation in each healthy stack: ALL angular columns. classify.
variable (o:Site c) (hp:81*w≤z) (hr:2*r≤w) (hg:2*z≤ k) (hC:4*r+16≤c.val) (hU : Healthy B.threshold (neighbors k o) V)
local notation "C₀" => (charm w r)
include hp Q hU hg
lemma jewelP (i: Stars) (x: Site (Y i)) : masked B.threshold (neighbors z (voyageL Q i x o)) (Trio.unitR Q fa i x (voyageL Q i x o)) V= unitR Q fa i x (voyageL Q i x o) V:= by
  apply masked_eq; exact hU.mono_left (parcelH Q z hp i x o hg)

variable (f₀ : Offer G c) (h₀:CompatibleP B r f₀ fa)
include hr h₀
lemma pricedH (i : Stars) (x: Site (Y i)) :
    let p:= voyageL Q i x o; let W:=Slide.shape (trackR Q i) p V
    unitR Q fa i x p V=fa i (Slide.ascended (Q i) x) W ∧ flags B.threshold W=∅ ∧
       Agrees (Lattice.box r) (expandAt (Slide.ascended (Q i) x) W) (Slide.thing (Slide.charm (w*roller i.val) r x) o V):= by
  intro p W; refine ⟨?_, Trio.hintQ Q z V i hp p (hU.mono_left (parcelH Q z hp i x o hg)), Slide.wandered (Q i) (hr.trans (plus_roll ..)) x o V⟩ -- order
  obtain ⟨v,hv⟩:= Slide.snap (Q i) x; rw [← hv, ← add_zero ((Slide.slant v).act x), show (Slide.slant v).act x+0=Lattice.affine (Slide.slant v) 0 x from rfl, ← h₀.moves]
  rw [show pull (Slide.slant v) 0 W=W from Slide.traps (Q i) v V p]; rfl
include hC
lemma sailing (hm:0<r) : unearthed B Q z fa o V=f₀ o V:= by
  choose x hx using Slide.presents (Q 0) (Z:=r) (hr.trans (plus_roll ..)) hm -- order edit
  let P (p: Petals r):= Trio.unitR Q fa (0:Stars) (x p) (voyageL Q 0 (x p) o) V
  have hk i y:= pricedH B Q z fa V o hp hr hg hU f₀ h₀ i y
  have hz (i:Stars) (x' : Site (Y i)): Trio.unitR Q fa i x' (voyageL Q i x' o) V=P (Slide.charm (w*roller i.val) r x'):= by
    let q:= charm (w*roller i.val) r x'; obtain ⟨hf,hQ,hJ⟩:= hk i x'; let y:=x q
    obtain ⟨ht,he,hh⟩:= hk 0 y; have hh' : charm (w*roller (0:Stars).val) r y=q:= hx q
    rw [hh'] at hh; change _=Trio.unitR Q fa 0 y _ V; rw [hf,ht]; apply h₀.pace _ _ _ _ _ _ hQ he; exact fun i hi hj=>(hJ i hi hj).trans (hh i hi hj).symm
  change (∑ i:Stars,glimmer w i*∑ y:Site (Y i),masked B.threshold _ _ V)= _
  simp_rw [jewelP B Q z fa V o hp hg hU,hz, Slide.vogue _ hm hr Q P]
  let x' := x (Slide.rosy r); let p:=voyageL Q 0 x' o; change Trio.unitR Q fa 0 x' p V=_
  obtain ⟨hz,hk,he⟩:= hk 0 x'; rw [hz]; rw [show charm (w*roller (0:Stars).val) r x'=Slide.rosy r from hx _,Slide.self] at he
  obtain ⟨T,hT,hL⟩:= Slide.shifts V o r (by omega) B.threshold B.threshold_pos.le (hU.mono_left (show neighbors r o ⊆ neighbors k o from (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))))
  exact Eq.trans (h₀.forks 0 _ o _ T hk hT (fun i hi hj=> (he _ hi hj).trans (hL _ hi hj).symm)) (h₀.visitL o T V (readNear o (by omega) hL))
end YM.PhysicalNext.Repeat.Trio
