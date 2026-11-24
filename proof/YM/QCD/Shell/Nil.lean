import YM.QCD.Shell.Shore
/-! # Real layer. hue dictionaries on arbitrary virtual-τ labels; convert only via corresponding j Tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
-- Hue bridge ANY δ.Surface.Mat. No wind.G.In when bads.
variable {E J:Type}[Countable E][Countable J] {d':Ratio c f}
variable (G₁:Rise f N E J)
open Flume YM.Next.Free Stew Leaf Jets.Touch Jets.Sun -- inspect
variable {d₂ D' K:ℕ}{z:Support f}{x:ℝ}
-- zeros priced by θ-root (Eyes/B.canvE), no wiggling Cf. works for empty κ.
open Dust
variable {F':Cash W s μ L Q o C T (lore (trimP T R δ β B₀))}
variable {D:Heir.Record}{u':ι}
lemma spareG {T:Forest S.ratio} (q: Config su f→ℝ)(he:q=fun _=>0)(χ:Chi)(p: BudgetPoint)(i:ℕ) (N':Libretto su j)(V:Grid c)(k:S.Choices) : Horn p N' F' T k χ D V i q 0:=by
    rw [he]; unfold Horn; intro z hz; refine ⟨contDiffAt_const,fun l hl A hA=>?_⟩; simp -- cart
variable (G':Send d' N (Tr f))(i:Finset (Fj (Tr f) E J))
variable (hT:Tone Y G' G₁ i u') {μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x₁ x₂ z κ ρ D₀:ℝ}
variable (hp: Peak G' R.threshold x y x₁ μ') (h:Cents G₁ σ Φ x R.threshold)(hz: G₁.Wave R.threshold)
variable (k' :ℕ) (hx: ( (lore (trimP T R δ β B₀)).activities.reg k').support= brimW G' G₁ i) (hs:x₂ ≤ y)(hv:0≤ x₂) (hρ:0<ρ)(hZ:0 < κ)
local notation "A'"=> Brim.plate F' k'
local notation "J!"=> G'
include N' F' hp hv hT hx h hz hρ hZ hs
lemma campR (χ:Chi)(D:Heir.Record)(ht:G'.trim ≤ radiusB s) (ha:coverNumber (radiusB s) (Brim.plate F' k').support ≤radiusB s):
    let p:=∏ j∈i, paidSet G' G₁ μ' σ Φ x₁ ρ κ 1 j
    Lore Y O N' F' χ D D₀ u' k' 0 ((1+(Malachite.radiusD s:ℝ))^2*((ρ⁻¹)^(leftE i).card*p)) 0 x₂:=by
    intro p; constructor; intro F y0 V P H he hV W X hW; refine ⟨fun _=>0,fun _ _ _=>rfl,measurable_const,fun _ _=> (norm_zero).le,fun U hu h=>?_,spareG _ rfl χ O _ _ V y0⟩
    have hp':Healthy R.threshold (brimW G' G₁ i) U:= hx ▸ hu
    have hk : hue G' G₁ R.threshold i U=dye G' G₁ R.threshold i U :=by rw [maskingW G' G₁ i hT.stops, masked_eq _ _ _ _ hp']
    have hz':= summing G' G₁ hp i U hz (β:=σ) (κ:=Φ) (by assumption)
    let g:= hue G' G₁ R.threshold i U; let f: Support c:= (halo G'.trim (coreW G' G₁ i)).image d'.parent
    have hX : Gated f g:=by unfold g; rw [hk]; exact halo_dye G' G₁ R.threshold i U hz f (Subset.refl f)
    have hh:f⊆ (A').support:=by
       change _⊆ yFoot S _ _ _; unfold yFoot; rw [hx]; intro i hi; apply halo_subset
       rw [hT.born]; refine image_subset_image (s₁:=halo G'.trim _) ?_ hi; rw [brim_eq]; exact Subset.trans (Corona.halo_mono (Nat.le_succ _) (Subset.refl _)) (Finset.subset_union_left)
    rw [hT.cash,sub_zero]; apply (he g.val).trans; apply (Stew.future _ hv hs _).trans; apply (shard (A').support (A').site (Malachite.radiusD s) (fun i hi=> (Corona.extent _ (radiusB s) hi (A').anchor).trans ?cost) g hp.cup (gateMon _ _ hh _ hX)).trans
    case cost => unfold Malachite.radiusD; gcongr
    apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [show p= _ from expensesW (υ:=1) G' G₁ i x₁ ρ κ,hT.stops,Finset.card_empty,Nat.add_zero,invSize,hT.stops, sum_empty,pow_zero,pow_zero,mul_one,mul_one, Nat.mul_zero,pow_zero,mul_one,← mul_assoc,← mul_pow,inv_mul_cancel₀ (by linarith),one_pow,one_mul]; apply hz'.trans_eq; unfold invSize; simp only [hT.stops,sum_empty, Nat.mul_zero,pow_zero,one_mul]
omit hp hx hρ hZ hv hs hz h
lemma darkness (χ:Chi)(O:BudgetPoint)(D:Heir.Record)(hs:i.Nonempty)(he:leftE i=∅): Lore Y O N' F' χ D D₀ u' k' 0 0 0 x₂:=by
    constructor; intro F y0 V P H he' hV _ p hG; refine ⟨fun _=>0,fun _ _ _=>rfl,measurable_const,fun _ _=>norm_zero.le,fun U hU _=>?_,spareG _ rfl χ O _ _ V y0⟩
    rw [hT.cash,nightly G' G₁ i hs he hT.stops]; simp
end YM.QCD.Shells
