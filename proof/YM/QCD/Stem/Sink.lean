import YM.QCD.Stem.Pitch
/-! # tail leases with angle probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure Precision ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove AnalyticBridge VerifiedReset
variable {C:Side}{D D' w j:ℕ}{d r t t' p p' η b z A:ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration Song Meadow
section stanches
variable (S:Gem c N I)(f:I→ℝ)
lemma wells (H : Licence B t p r S) (hv:η ≤t) (ht:p≤ t'):Licence B η t' r S:=by
   obtain ⟨x,hx,h⟩:=H.zone; refine ⟨x,fun i=> ?_,h⟩; apply budget_loosen _ ht ; refine budget_mono (hx i) ?_ ?_
   · intro j; split; exact mul_nonneg (h j).travel (Real.exp_pos _).le; exact le_rfl
   intro j; split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _))) (h j).travel; exact le_rfl
variable (X:I→Prop)(Y: ℕ→I→Prop)
lemma rim (he : Anchored (fun i=> (S.addr i).site) f (fun i=> coverNumber w (S.addr i).support) t A)(hr:0 < r)(hv:∀ i,∀ᶠ k in atTop, ¬ Y k i): ∀ᶠ k in atTop, Anchored (fun i=>(S.addr i).site) (fun i=> if Y k i then f i else 0) (fun i=>coverNumber w (S.addr i).support) t r:=by
   refine eventually_all.mpr fun x=>?_; let u i:= if (S.addr i).site=x then f i*Real.exp (t*coverNumber w (S.addr i).support) else 0; let p k i:=if Y k i then u i else 0; have hu : SumBudget u A:= he x
   have H k i:0 ≤ p k i:=by unfold p; split; exact hu.1 i; rfl
   have ht k i:p k i≤u i:=by unfold p; split; rfl; exact hu.1 i
   have hx i:Tendsto (fun k=>p k i) atTop (𝓝 0):= tendsto_const_nhds.congr' ((hv i).mono fun k hk=> (if_neg hk).symm)
   have hh:= tendsto_tsum_of_dominated_convergence hu.2.1 hx (Eventually.of_forall (fun k i=> (show ‖p k i‖≤ u i from (by rw [Real.norm_of_nonneg (H k i)]; exact ht k i))))
   rw [tsum_zero] at hh; filter_upwards [hh.eventually_le_const hr] with k hk
   have hz: SumBudget (p k) r:= ⟨H k,hu.2.1.of_nonneg_of_le (H k) (ht k),hk⟩
   convert hz using 2 with i; unfold p u; split <;> split <;> simp_all
-- radial tariff
structure Scaled (h:ℝ)(g:I→ℕ)(B:BudgetPoint)(S:Gem c N I)(t p r:ℝ):Prop where
 milk :∃ f:I→ℝ,(∀ i,Woven (S.addr i).site (S.addr i).support B r (S.view i) (f i)) ∧ Anchored (fun i=>(S.addr i).site) (fun i=> f i*Real.exp (h*g i)) (fun i=>coverNumber B.B (S.addr i).support) t p
variable (P:I→ℕ)(hh : Scaled b P B S t p r)(hp:0≤b)
include hh hp
lemma turtle : Licence B t p r S:=by
   obtain ⟨x,hx,h⟩:= hh.milk; refine ⟨x,fun i=>?_,hx⟩; refine budget_mono (h i) (fun j=>?_) (fun j=>?_)
   · split; exact mul_nonneg (hx _).travel (Real.exp_pos _).le; exact le_rfl
   split; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (hx _).travel (Real.one_le_exp (mul_nonneg hp (Nat.cast_nonneg _)))) (Real.exp_pos _).le; exact le_rfl
lemma skyline (W:ℕ→I→ Prop) (hr:0<t') (hv:∀ i, P i ≤ n →∀ᶠ k in atTop, ¬ W k i): ∀ᶠ k in atTop, Licence B t (Real.exp (-b*n)*p+t') r (Moss.muteK S (W k)) :=by
    obtain ⟨x,hx,H⟩:=hh.milk; obtain ⟨x',hH,-⟩:= (turtle S P hh hp).zone
    let g i:=if n < P i then x i else 0; let Y k i:= P i≤ n ∧ W k i; let s:=fun i=> (S.addr i).site; let l i:=coverNumber B.B (S.addr i).support; have hg i:0≤ g i:=ite_nonneg (hx i).travel le_rfl
    have hs : Anchored s g l t (Real.exp (-b*n)*p):=by
       intro i; apply budget_mono (budget_scale (Real.exp_pos _).le (H i))
       · intro i; split; exact mul_nonneg (hg i) (Real.exp_pos _).le; exact le_rfl
       intro j; split
       next hv=> unfold s at hv; dsimp only; unfold g; split
                 next hi => rw [←mul_assoc (Real.exp _),mul_left_comm (Real.exp (-b*(n:ℝ))),←Real.exp_add]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (hx _).travel (Real.one_le_exp (by rw [neg_mul]; have h:=mul_le_mul_of_nonneg_left (show (n:ℝ)≤P j from Nat.cast_le.mpr hi.le) hp; linarith))) (Real.exp_pos _).le
                 next hq=>have h:= (hx j).travel; rw [zero_mul]; positivity
       next hv=>unfold s at hv; rw [mul_zero]
    have hy : Anchored s x l t p:=by
       intro i; refine budget_mono (H i) (fun i=> ?_) (fun i=> ?_)
       · split; exact mul_nonneg (hx _).travel (Real.exp_pos _).le; exact le_rfl
       split; next h=> unfold s at h; dsimp only; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (hx _).travel (Real.one_le_exp (by positivity))) (Real.exp_pos _).le
       next h=> unfold s at h; rfl
    have he i:∀ᶠ k in atTop, ¬ Y k i:=by by_cases he:P i≤ n; exact (hv i he).mono fun k h hx=> h hx.2; exact Eventually.of_forall fun i hz=> he hz.1
    filter_upwards [rim S x Y hy hr he] with k hK; let q i:= if Y k i then x i else 0; have hq i:0 ≤ q i:=ite_nonneg (hx _).travel le_rfl
    refine ⟨g+q,fun i=>?_,fun i=>?_⟩
    · convert budget_plus (hs i) (hK i) using 2 with j; change ite (s j=i) ((g+q) j * Real.exp (t*l j)) 0=(ite (s j=i) _ 0 +if s j=i then _ else _); split; next h=> rw [Pi.add_apply,add_mul]; unfold q; by_cases he: Y k j <;> simp [he,l]
      next _=> rw [add_zero]
    rw [eitherX]; split
    next h=> refine (hx i).stretches (Subset.refl _) ?_; change x i≤ g i+ q i; by_cases ht:n<P i; · rw [show g i=x i from if_pos ht]; exact le_add_of_nonneg_right (hq _)
             rw [show q i=x i from if_pos ⟨Nat.le_of_not_gt ht,h⟩]; exact le_add_of_nonneg_left (hg _)
    next h=> exact (Moss.freeK ..).stretches (Subset.refl _) (add_nonneg (hg i) (hq i))
end stanches
section path
variable (R:PathData su)(O:Clip)
set_option quotPrecheck false
local notation "G"=>sax R O B c N t p
open Quotes
lemma enough (h:R.Bounds O r d p')(hz:WilsonStartup.Decent O B)(he:0≤t')(hp: preExponent B/B.B≤r/4) : Dyed (G) ∧ Scaled (r/4) (fun i:Rake c=> melody R i.2) B (G) (preExponent B) (Song.octaveNeed su B O r d p' t p) t':=by
    obtain ⟨f,hv,hh⟩:= lent (c:=c) B R O t p h hz hp; let d:= rollers c; have hf i:= (hh (d i)).1
    refine ⟨⟨fun i U k=>?_,fun i U W hx=> Reggae.thorough ..,fun i U=> Reggae.thorough ..⟩, f ∘ d,fun i=> wealthy N _ _ _ (hf i) (hh (d i)).2 he,fun x=>?_⟩
    · refine congr_arg Subtype.val (show sways (Lat.rotates N k) (Reggae.ocean _ _ _)=(G).view i U from ?_); rw [Reggae.thorough]; exact congr_arg _ ((hf i).symmetry k U)
    convert Extra.Iteration.Cost.equiv d (hv x) using 2 with i; dsimp only [Function.comp_apply]; change ite _ ((f _ * _)*_) _= ite (((G).addr i).site=x) ((f _*Real.exp (r/4*arc R (d i)))*_) _; rw [show arc R (d i)= melody R i.2 from arc_receipt ..]; try rfl
lemma upward (i:Rake c)(h:melody R i.2 ≤ n):∀ᶠ k in atTop,i∈keepP R c n k:= (burgeoning _ _ _ h).mono fun k hk=> mem_product.mpr ⟨mem_univ _,hk⟩
end path
end YM.QCD.Stem
