import YM.Next.ROTATIONS.Symbol
import YM.Gust.Cav.OJournal
import YM.Gust.Cav.OCharge
/- Variant of YM.Next.ROTATIONS.Symbol, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}
private lemma pair_head (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S)
    (v w : S.Tag) (T : Panels) (a i) (D) (ht : ScaleCap D (pair v w))
    (hh : ScaleCap D (pair (Ward.rise P a v) w)) (hF : flat (D+1) (T i)) :
    integral volume (fun x => pair v w x*tensor (moved a T) x)= - ∫ x, pair (Ward.rise P a v) w x*tensor T x := by
  have hk : flat D (T i) := fun j hv => hF j (by omega)
  have hx : flat D (moved a T i) := by
    unfold moved; by_cases h : i=a
    · subst i; rw [update_self]; exact prime_zero_order D (T a) hF
    rw [Function.update_of_ne h]; exact hk
  refine integrate_both _ (tensor T) _ _ a (radical T D i hk _ ht (pair_meas H ..)) (radical _ D i hx _ ht (pair_meas H ..))
    (radical T D i hk _ hh (pair_meas H ..)) (pair_dif H v w P hp a) (fun x _ y => ?_)
  exact moved_deriv ..
structure Strong (J : Stress S) (P : DiffPlan S) (D : ℕ) : Prop where
  bound a b c d : ScaleCap D (linePair J a b c d)
  total a b c d : ScaleCap D (pair (Ward.rise P a (tag J a b)) (tag J c d))
lemma stronger (H : S.Hierarchy) (J : Stress S) (P : DiffPlan S) : ∃ D : ℕ,0<D ∧ Strong J P D := by
  let t (i : Axis × Axis × Axis × Axis) (n : ℕ) := ScaleCap n (linePair J i.1 i.2.1 i.2.2.1 i.2.2.2) ∧
       ScaleCap n (pair (Ward.rise P i.1 (tag J i.1 i.2.1)) (tag J i.2.2.1 i.2.2.2))
  have he : ∀ᶠ D in atTop, ∀ i,t i D := by
    refine eventually_all.mpr fun i => ?_; rcases i with ⟨a,b,c,d⟩
    obtain ⟨x,hx⟩ := pair_bound H (tag J a b) (tag J c d)
    obtain ⟨y,hy⟩ := pair_bound H (Ward.rise P a (tag J a b)) (tag J c d)
    filter_upwards [eventually_ge_atTop x,eventually_ge_atTop y] with n h k
    exact ⟨hx.loosen h,hy.loosen k⟩
  obtain ⟨D,hD,h⟩ := ((eventually_gt_atTop (0:ℕ)).and he).exists
  exact ⟨D,hD,⟨fun a b c d => (h (a,b,c,d)).1,fun a b c d => (h (a,b,c,d)).2⟩⟩
lemma closed_shell (H : S.Hierarchy) (P : DiffPlan S) (h : P.Derivatives S) {J : Stress S} {D : ℕ} {R : Series}
    (hp : Portrait J D R) (he : Conserved P H.spin J) (hS : Strong J P D) :
    ∀ b c d (f : Panels) i, flat (D+1) (f i) → delta R b c d f = 0 := by
  intro b c d f i hi
  let g (a) := pair (Ward.rise P a (tag J a b)) (tag J c d)
  have hk : flat D (f i) := fun k h => hi k (by omega)
  have hv a : flat D (moved a f i) := by
    unfold moved; by_cases h:i=a; · subst a; rw [update_self]; exact prime_zero_order D (f i) hi
    rw [update_of_ne h]; exact hk
  have hx a : R a b c d (moved a f)= -(∫ x,g a x*tensor f x) := by
    rw [hp.agrees a b c d (moved a f) i (hv a)]
    exact pair_head H P h _ _ f a i D (hS.bound ..) (hS.total ..) hi
  have hh a : Integrable (fun x => g a x*tensor f x) := radical _ D i hk _ (hS.total ..) (pair_meas H ..)
  have hf x : ∑ a,g a x=0 := by
    let w := tag J c d
    let z : Fin 2 → S.Tag := ![⟨4,J c d⟩,w]
    let T := points ![x,0]
    have heq a : g a x= here z T 0 5 (P.deriv 4 a (J a b)) := by
      rw [takes]; unfold g pair; congr 2; ext1 i; fin_cases i <;> simp [tag,z,w,Ward.rise]
    simp_rw [heq]; rw [← _root_.map_sum, he.divergence,map_zero]
  rw [delta_at]; simp_rw [hx,Finset.sum_neg_distrib,← integral_finsetSum _ (fun i _ => hh i)]
  simp_rw [← Finset.sum_mul,hf]; simp
lemma pupils (H : S.Hierarchy) (P : DiffPlan S) (h : P.Derivatives S) {J : Stress S} {D : ℕ} {R : Series}
    (hp : Portrait J D R) (he : Conserved P H.spin J) (hS : Strong J P D) (b c d f) :
    delta R b c d f = delta R b c d (projections f (D+1)) := by
  let T (s : Finset Axis) (j : Axis) := if j∈s then collect (D+1) (f j) else f j
  let A := delta R b c d
  have hh (s : Finset Axis) : A f = A (T s) := by
    induction s using Finset.induction_on with
    | empty => simp [T]
    | insert i s hi ih =>
      rw [ih, show T (insert i s)=Function.update (T s) i (collect (D+1) (f i)) from funext fun k => by by_cases h:k=i <;> simp [T,h]]
      let p := f i-collect (D+1) (f i)
      have hp : A (update (T s) i p)=0 := closed_shell H P h hp he hS b c d _ i (by rw [update_self]; exact missed (D+1) (f i))
      change A (_)=A _; unfold p at hp; rw [A.map_update_sub,sub_eq_zero] at hp
      rw [show f i=T s i from by simp [T,hi],update_eq_self] at hp
      simpa [T,hi] using hp
  have ht : T Finset.univ=projections f (D+1) := by ext1 i; simp only [T, projections,Finset.mem_univ,ite_true]
  rw [← ht]; exact hh _
lemma source_cost (H : S.Hierarchy) (P : DiffPlan S) (h : P.Derivatives S) {J : Stress S} {D : ℕ} (hd : 0<D) {R : Series}
    (hp : Portrait J D R) (he : Conserved P H.spin J) (hS : Strong J P D) (a : ℝ) (ha : a≤0) (b c d) (w : Axis→ℝ) (hw : ∀ i,w i ≤ a)
    (f : Grouping) : Budget (a*3) (fun n => source (joint R) b c d (mails w f n)) :=
  (lifted_cost a ha hw (pupils H P h (joined hp hd) he hS b c d) (joint_null hp hd b c d)).times I
end YM.Spiral.Outer

