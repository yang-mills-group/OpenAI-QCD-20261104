import YM.Massive.Reservoir.Prior
import YM.QCD.Agate.Sink
import YM.QCD.Agate.Limbs
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Haar local-trace norm pricing and separability for the algebra of
all gauge-invariant bounded Borel pencils on an arbitrary Lot (finite set
of sites in the lattice cover). `books` approximates by a countable *subset
of these pencils*, at the precision of this bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate.Supply
open Plum Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical ENNReal
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet Plum.Small
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)} {S D Y:Lot}

noncomputable def shelves (D:Lot): Measure (Trace D):= Measure.pi (fun _=> su.probHaar)
instance : IsProbabilityMeasure (shelves D):=by unfold shelves; infer_instance

private theorem integral_trace (p:Site c)(h:Fits c D)(f:Trace D→ℝ) :
    (∫ U,f (crest p U) ∂prior su c) = ∫ U,f U ∂shelves D:=by
    let s:Pipe D↪Edge (Site c):=⟨strike p,crested p h⟩
    have hs(U:Grid c): crest p U=U∘ ⇑s:=rfl
    apply Complex.ofReal_injective
    have he(f:Grid c→ℝ): (∫ i:Grid c,(f i:ℂ) ∂prior su c)= ((∫ i,f i∂prior su c):ℝ):= integral_ofReal (𝕜:=ℂ)
    have hg: (∫ i:Trace D,(f i:ℂ)∂shelves D) = ((∫ i,f i∂shelves D):ℝ):= integral_ofReal (𝕜:=ℂ)
    rw [← hg,←he (fun i=> f (crest p i))]; change (∫ i:Grid c,((f (i ∘ ⇑s)):ℂ)∂prior su c)=_; have H:= LocalCup.shelf (μ:=su.probHaar) s (fun V=> (f V:ℂ)) (fun _ _=> 1) (by intro i; simp); simp only [Finset.prod_const_one,one_mul] at H; exact H

noncomputable def budget (x:Malt D F):ℝ:= ∫ U,‖x.val U‖ ∂shelves D
lemma within (x:Malt D F)(p:Site c)(h:Fits c D): Covers (budget x) (visit p x):=by
    change Small.bill _ ≤ _; have he:= integral_trace p h (fun U=> ‖x.val U‖)
    apply (integral_mono (((palps p x).hp.intg (prior su c)).norm) ((((staysP x).travel ((crestC p).measurable)).intg (prior su c)).norm) (fun i=> (Land.pass_price (pensI p h) (x.val (crest p i))))).trans_eq he
lemma budget_sup {x:Malt D F}(hp:Coast w x): budget x≤w :=
    (integral_mono (((staysP x).intg (shelves D)).norm) (integrable_const (μ:=shelves D) w) hp).trans (by simp)

/-- Sequence version of chess localization bound. Note the quantifier for
location on torus, for every pixel with the hypotheses, and that pricing is
at local trace alone. -/
theorem bids (D:Lot)(s:ℕ→Side)(he:Tendsto (fun i=>(s i).val) atTop atTop)(hp:∀ᶠ i in atTop,Even (s i).val)(K:ℝ)(J:Patch)(F:ℕ) :
    ∃ A:ℝ,0<A ∧ ∀ᶠ i in atTop,∀ (P:Pixel (s i) F)(p: Site (s i)), Healing J P→ Continuous P→ Cvol P=1 →(∀ U, ‖P U‖ ≤ Globe.expo K (s i)) → ∀ Z:Malt D F, ‖fresh P (visit p Z)‖ ≤ A*budget Z:=by
    obtain ⟨r,hR⟩:= spade D s he; refine ⟨quota J r K,Real.exp_pos _,?_⟩
    filter_upwards [gravity D s he,hR,hp,he.eventually (eventually_ge_atTop (r+2*longM J)),he.eventually (eventually_ge_atTop 4)] with i hk hh hi hr h4 U p hU hx hv hA Z
    obtain ⟨q,hq⟩:=hh p; exact Small.planetary hU hx hv hi h4 q hr _ ((palps p Z).high hq) (within Z p hk) K hA

noncomputable abbrev Costs (D:Lot)(F:ℕ):Type:= Lp (Poly D F) 1 (shelves D)
noncomputable def book (x:Malt D F): Costs D F:= ((staysP x).intg (shelves D)).toL1 x.val
lemma budget_book (x:Malt D F) : ‖book x‖ = budget x:= L1.norm_of_fun_eq_integral_norm _
lemma budget_dist (x y:Malt D F) : budget (x-y)= dist (book x) (book y):=by
    rw [dist_eq_norm,← budget_book,show book (x-y)=_ from (Integrable.toL1_sub x.val y.val ((staysP x).intg (shelves D)) ((staysP y).intg (shelves D)))]; rfl

set_option maxHeartbeats 650000 in
/-- There is one sequence of such tests (per region) dense in all `Malt`
at integral cost. -/
theorem books (D:Lot)(F:ℕ) : ∃ p:ℕ→Malt D F,∀ (x:Malt D F)(u:ℝ),0<u→∃ i:ℕ,budget (x-p i) < u:=by
    haveI : Fact ((1:ℝ≥0∞)≠⊤):= ⟨by norm_num⟩
    let T:= ↥(Set.range (book (D:=D) (F:=F)))
    letI : Nonempty T:=⟨⟨book (1:Malt D F),1,rfl⟩⟩
    haveI : SecondCountableTopology (Trace D):=inferInstance
    haveI : MeasurableSpace.CountablyGenerated (Trace D):=inferInstance
    haveI : MeasureTheory.IsSeparable (shelves D):=MeasureTheory.isSeparable_of_sigmaFinite _
    haveI : TopologicalSpace.SeparableSpace (Poly D F):= inferInstance
    haveI : SecondCountableTopology (Costs D F):= inferInstance
    let q:= TopologicalSpace.denseSeq T
    choose p H using fun i:ℕ=> show ∃ x,book x=(q i).val from (q i).property
    refine ⟨p,?_⟩; intro x v hv; let b:T:= ⟨book x, x,rfl⟩
    obtain ⟨i,hi⟩:= Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq T) b v hv
    refine ⟨i,?_⟩; rw [budget_dist,H]; exact hi
end YM.QCD.Agate.Supply
#print axioms YM.QCD.Agate.Supply.bids
#print axioms YM.QCD.Agate.Supply.books
