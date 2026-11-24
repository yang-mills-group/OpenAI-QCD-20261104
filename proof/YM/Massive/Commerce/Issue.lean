import YM.QCD.Calm.Forest
import YM.Massive.Commerce.Plain

/-! # Updating just E,K amplitudes does *not* alter the forest geometries
This is useful in proofs about multi-parameter families all on the same path
with the same chosen underlying label supports. Formulate with `Fleet` first. -/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
local notation "V'"=> prism T τ
open Art Blaze Polar Shield Frond

open GasP Ursell Graph
variable (f':ι→Grid f→Grid c→EvenA c N) (A:ι → Prop)

/-- Changes *only* `works`, new supports, exclusion overlaps, frame etc identical. -/
abbrev version : Fleet H ι N := {Y with works:=f'}
-- Explicit reader variants so one can use `rfl` under reduction.
local notation "V₁"=> version Y f'
variable {χ: Chi}
example (i:Y.Bright) : (V₁).Bright:=i
example (i:Y.Faber) : (V₁).Faber:=i
example (i:Y.Bright) : lightF Y i= lightF (V₁) i:=rfl

lemma band_silent (z:I)(X:Coat T F)(hz:∀ i∈z.toRight, f' i=Y.works i) : bandL (V₁) z X=bandL Y z X:=by
    unfold bandL; let Q:= Y.suitcase F
    change ite (Ac.Spark Q.gP z ∧ Q.born z) _ _=ite (Ac.Spark Q.gP z ∧ Q.born z) _ _
    split
    swap; · rfl
    apply congr_arg; funext i
    let i₀:= podium S su (Y.fullA z) (radiusB τ); let W:= (preps X (roster z.toLeft)).taggedL i
    change lows (V₁) i₀ z W= lows Y i₀ z W
    unfold lows; apply integral_congr_ae; filter_upwards with t
    apply integral_congr_ae; filter_upwards with y
    simp only [regards]; apply congr_arg; apply congr_arg; refine Finset.prod_congr rfl ?_
    intro i hi; change _ • f' i _ _ = _ • Y.works i _ _; rw [hz i hi]

lemma brisk_silent (z:I)(U:Grid c)(hz:∀ i∈z.toRight, f' i=Y.works i) : (V₁).brisk z χ U=Y.brisk z χ U:=congr_arg choiceS (funext (fun _=> band_silent Y f' z _ hz))

lemma nameless (z:Clusters Y.Bright) (W:Clusters Y.Bright→ RegularAddress c)(hY:∀ i, ¬ A i→ f' i= Y.works i) (hz:¬ King.stand Y A z) : (Patron.crude V₁ χ W).view z= (Patron.crude Y χ W).view z :=by
    apply funext; intro U; change Patron.pepper (fun V=> furnace V₁ χ V z) U=Patron.pepper (fun V=> furnace Y χ V z) U; refine congrFun (congr_arg Patron.pepper (funext fun V=> ?_)) U
    unfold furnace termP
    apply congr_arg; apply congr_arg; exact prod_congr rfl fun i _=> brisk_silent Y f' _ V (fun j h=> hY j (fun h'=>hz ⟨i,j,h,h'⟩))
end YM.QCD.Loom.Fleet

-- Keep all but the ExtraK singleton families. In particular don't count only
-- forest-overlap with a fixed shape; any nonprincipal structure comparing the
-- two forests is charged by their higher-cost Dated allowance. Large ε for
-- readability not required here.
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat Moss PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
open Fleet Port Run Leaf Tee Orbit Garden Jets Flume YM.Next.Free
open GasP Ursell Graph Patron Stew
open Blaze King Sands
local notation "I'"=> ι⊕ Varn f c ⊕ Gaze c
variable (Y:Fleet H (ι⊕Varn f c⊕Gaze c) N) (f': (ι⊕Varn f c⊕Gaze c)→Grid f→Grid c→EvenA c N)
local notation "V₁"=> version Y f'
set_option quotPrecheck false -- move up?
variable (χ:Chi) {j k:ℕ} {a h:ℝ}
def first (i:Clusters Y.Bright):Prop:= ∃ q:Y.Bright,∃ j:ι,i=individual q ∧ Aliased Y q (.inl j)
lemma careless (p:Clusters Y.Bright) (A:Clusters Y.Bright→RegularAddress c) (hE:¬ first Y p) (hD:¬ Dated Y Fury nectarP τ p) (hg:∀ i:I', ¬nectarP i → f' i= Y.works i) : (crude V₁ χ A).view p = (crude Y χ A).view p:=by
    apply nameless Y f' nectarP p A hg
    intro hz; have hh:¬ 2≤ crestP Y p:= fun h=> hD (Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨h,hz⟩)
    obtain ⟨q,i,h1,h2,h3⟩:= Moss.individualH Y p (by omega) nectarP hz
    exact hE (by rcases i with i|i; exact ⟨q,i,h1,h3⟩; exact False.elim h2)
lemma Wminus {t₁ t₂:ℝ} {q:Site c}{X:Support c}{P:BudgetPoint} (u v:Grid c→EvenA c N) (hA:Woven q X P h u t₁) (hW:Woven q X P h v t₂): Woven q X P h (u-v) (t₁+t₂):=by
    simpa only [neg_one_smul,norm_neg,norm_one,one_mul,sub_eq_add_neg] using hA.addition (hW.byScalar (-1))
lemma charge_sum_hit {ι:Type*} (X:ι→Support f) (g p:ι→ℝ)(n:ℕ)(h:Ac.Hit X n g a δ)(he: Ac.Hit X n p a β) : Ac.Hit X n (fun i=>g i+p i) a (δ+β):=by
    intro i; convert! Local.sumBudget_add (h i) (he i) using 1; funext x; by_cases h:i∈ X x <;> simp only [h, ↓reduceIte,add_mul,add_zero]
lemma Wzero {q:Site c}{X:Support c}{P:BudgetPoint}(h:ℝ): Woven q X P h (0:Grid c→EvenA c N) 0:=by
  simpa only [sum_empty] using Woven.sumX (o:=q) (p:=P) (N:=N) (B:=X) (a:=h) (fun _:ℕ=>0) ∅ (fun _=>0) (by simp)
/-- `Woven`/`Hit` price as tight as `jelly` on the *whole* nonprincipal
 part of a change in E,K. Even at the very same index set and chosen Cash,
 unprojected supplements pointwise before any required repackaging at
 shifted anchors and failure coalescence. This gives a bound, not a Lip
 estimate; later for perturbations it should be usable in Cauchy-type
 estimates. -/
lemma advance_bound (hY: Gosh Y χ a h j k) (hV:Gosh V₁ χ a h j k)
    (h₀:∀ i:I', ¬ nectarP i → f' i= Y.works i) : ∃ g:Clusters Y.Bright→ℝ,
    (∀ (W:Clusters Y.Bright→ RegularAddress c) (P:BudgetPoint), (∀ i,(W i).support=seatP Y.lightF i) → P.order=j→P.power=k→P.B=radiusB τ→P.threshold=Pressure.temp τ→∀ i, Woven (W i).site (seatP Y.lightF i) P h (if first Y i then 0 else (crude V₁ χ W).view i-(crude Y χ W).view i) (g i)) ∧ Ac.Hit (seatP Y.lightF) (radiusB τ) g a (2*jelly L τ):=by
    obtain ⟨b,hb,-,h⟩:=hV.bills
    obtain ⟨p,hp,-,hh⟩:= hY.bills
    let x i:= Dated Y Fury nectarP τ i
    let T1 (i:Clusters Y.Bright):=if x i then b i else 0
    let T2 (i:Clusters Y.Bright):= if x i then p i else 0
    have he: Ac.Hit (seatP Y.lightF) (radiusB τ) T1 a (jelly L τ):= h
    refine ⟨fun i=>T1 i+T2 i, ?_,by rw [two_mul]; exact charge_sum_hit _ T1 T2 _ he hh⟩
    intro W P h₁ h₂ h₃ h₄ h₅ i
    have hv := hp P W h₁ h₂ h₃ h₄ h₅ i; have hhB:=hb P W h₁ h₂ h₃ h₄ h₅ i
    by_cases hi: first Y i
    · rw [if_pos hi]; apply (Wzero _).stretches (Subset.refl _); unfold T1 T2; exact add_nonneg (ite_nonneg hhB.travel le_rfl) (ite_nonneg hv.travel le_rfl)
    rw [if_neg hi]; dsimp only [T1,T2]; by_cases hx:x i
    · rw [if_pos hx,if_pos hx]; exact Wminus _ _ hhB hv
    rw [if_neg hx, if_neg hx, careless Y f' χ i W hi hx h₀, sub_self, add_zero]; exact Wzero _
end YM.QCD.Loom
#print axioms YM.QCD.Loom.advance_bound
