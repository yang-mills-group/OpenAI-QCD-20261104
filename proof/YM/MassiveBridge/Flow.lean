import YM.MassiveBridge.Cap
/-!
# Flows on the cap Hilbert space

As in the Yang-Mills `YM.OS.Flow/Dynamics`; doesn't need boosts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter Analysis
open Fields (pointMoment)
open OS (Cross)
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder ComplexConjugate
variable {F : Fields} {a : Axis} {S : F.Kernel}

lemma nonnegative (H : Fields.Euclidean S) (h : Involutive (F.adj a)) : NNKernel (fun (x y : Future F a) => kernel S a x.val y.val) := by
  apply NNKernel.criterion
  · intro x y
    change star (pointMoment S _) = pointMoment S _
    rw [← H.conjugate a _ (twoSides y.property x.property), show Fields.reflect a (reflect y.val a ++ x.val) = reflect x.val a ++ y.val from by rw [show Fields.reflect a (reflect y.val a ++ x.val)=reflect x.val a ++ reflect (reflect y.val a) a by simp [reflect, Fields.reflect],reflect_twice a h]]
  intro m x c; exact H.rp a m (fun i => (x i).val) (fun i => (x i).property) c

abbrev Schwinger {F : Fields} (S : F.Kernel) (a : Axis) := YM.Kernel.Gram fun (x y : Future F a) => kernel S a x.val y.val
lemma schwinger_ready (H : Fields.Euclidean S) (h : Involutive (F.adj a)) : Nonempty (Schwinger S a) := YM.Kernel.host (nonnegative H h)

variable (X : Schwinger S a)
lemma nil_norm (H : Fields.Euclidean S) : ‖X.plant (air a)‖=1 := by
  have hx := X.measure (air a) (air a)
  have hw : kernel S a (air a).val (air a).val = 1 := by
    suffices hall : ∀ x f, S 0 x f=1 from hall _ _
    intro x f; rw [Subsingleton.elim x 0, Subsingleton.elim f 0]; exact H.empty
  rw [hw] at hx; rw [@norm_eq_sqrt_re_inner ℂ, hx]; simp
abbrev Voice (F : Fields) (a : Axis) := Future F a →₀ ℂ

def timed (t : ℝ≥0) : Voice F a →ₗ[ℂ] X.H := Finsupp.linearCombination ℂ (fun x => X.plant (travel x t))
def offAxis (u : Cross a) : Voice F a →ₗ[ℂ] X.H := Finsupp.linearCombination ℂ (fun x => X.plant (over x u))

lemma symmetrical (h : Fields.Euclidean S) (t u) (p q : Voice F a) :
    inner ℂ (timed X t p) (timed X u q) = inner ℂ (X.stems p) (timed X (u+t) q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single x c =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,inner_add_right,hf,hg]
    | single y d =>
      simp only [timed,Kernel.Gram.stems,Finsupp.linearCombination_single, inner_smul_left, inner_smul_right,
        X.measure, sym_time h a x (travel y u), advances]

lemma bothside (h : Fields.Euclidean S) (u) (p q : Voice F a) : inner ℂ (offAxis X u p) (offAxis X u q) =
    inner ℂ (X.stems p) (X.stems q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single x c =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,inner_add_right,hf,hg]
    | single y d =>
      simp only [offAxis,Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left,inner_smul_right,X.measure,
        sym_space h a]

lemma sq_key (v : X.H) : ‖v‖^2 = ‖inner ℂ v v‖ := by rw [inner_self_eq_norm_sq_to_K]; simp

lemma safe (u : Cross a) (H : Fields.Euclidean S) (p : Voice F a) : ‖offAxis X u p‖ = ‖X.stems p‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq_key X,sq_key X, bothside X H]

lemma enough (H : Fields.Euclidean S) (p : Voice F a) : ∃ R : ℝ, ∀ t, ‖timed X t p‖ ≤ R := by
  induction p using Finsupp.induction_linear with
  | zero => exact ⟨0,fun _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨A,hA⟩ := hf; obtain ⟨B,hB⟩ := hg
    refine ⟨A+B,fun t => ?_⟩
    rw [map_add]; exact (norm_add_le ..).trans (add_le_add (hA t) (hB t))
  | single w c =>
    obtain ⟨B,hB⟩ := (correl H a w w).2
    have he (t : ℝ≥0) : ‖X.plant (travel w t)‖^2 ≤ B := by
      rw [sq_key X,X.measure, sym_time H, advances]
      exact hB _ (by simp)
    refine ⟨‖c‖ * √B,fun t => ?_⟩
    rw [timed, Finsupp.linearCombination_single,norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact ((Real.le_sqrt (norm_nonneg _) (le_trans (sq_nonneg _) (he t))).mpr (he t))

/-- Doubling bounds. Sup trick: take sup over all t, so no large-power calculation. -/
lemma contract (H : Fields.Euclidean S) (t) (p : Voice F a) : ‖timed X t p‖ ≤ ‖X.stems p‖ := by
  let d i := ‖timed X i p‖
  have ht : BddAbove (Set.range d) := by
    obtain ⟨A,hA⟩ := enough X H p; exact ⟨A,by rintro _ ⟨y,rfl⟩; exact hA y⟩
  let c := ⨆ i : ℝ≥0, d i
  have he i : d i ≤ c := le_ciSup ht _
  have hp : 0 ≤ d t := norm_nonneg _
  have hh (i) : d i ^ 2 ≤ ‖X.stems p‖ * c := by
    change ‖timed X i p‖^2 ≤ _
    rw [sq_key X, symmetrical X H]
    exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (he _) (norm_nonneg _))
  let A := ‖X.stems p‖*c
  have hA : 0 ≤ A := le_trans (sq_nonneg _) (hh t)
  have h₀ := hp.trans (he t)
  have hw : c ≤ √A := ciSup_le fun i => (Real.le_sqrt (norm_nonneg (timed X i p)) hA).mpr (hh i)
  apply (he t).trans
  have hq := sq_le_sq₀ h₀ (Real.sqrt_nonneg A) |>.2 hw
  rw [Real.sq_sqrt hA] at hq
  dsimp only [A] at hq
  nlinarith [norm_nonneg (X.stems p)]

lemma strong {Y : Type*} [TopologicalSpace Y] {D : Hilbert} {f : Y → X.H.space →L[ℂ] D.space}
    (hp : ∀ x, ‖f x‖ ≤ 1) (h : ∀ i, Continuous fun x => f x (X.plant i)) : ∀ v : X.H, Continuous fun x => f x v := by
  have he (v : Voice F a) : Continuous fun x => f x (X.stems v) := by
    induction v using Finsupp.induction_linear with
    | zero => simp only [map_zero]; exact continuous_const
    | add i j hi hj => simp_rw [map_add]; exact hi.add hj
    | single i c => simp_rw [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul]
                    exact continuous_const.smul (h i)
  intro v
  refine continuous_iff_continuousAt.mpr fun x => Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨g,hg,H⟩ := Metric.mem_closure_iff.mp (X.whole v) (ε/4) (by positivity)
  obtain ⟨u,rfl⟩ := hg
  have hw (y) : dist (f y v) (f y (X.stems u)) < ε/4 := by
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt ((f y).le_opNorm _ |>.trans (mul_le_of_le_one_left (norm_nonneg _) (hp y)))
      (by simpa [dist_eq_norm] using H)
  filter_upwards [Metric.tendsto_nhds.mp (show ContinuousAt (fun x => f x (X.stems u)) x from (he u).continuousAt).tendsto (ε/4) (by positivity)] with y hy
  have hu := dist_triangle (f y v) (f y (X.stems u)) (f x (X.stems u))
  have hg := dist_triangle (f y v) (f x (X.stems u)) (f x v)
  change dist (f y v) (f x v)<ε
  have h₁ := hw y
  have h₂ := hw x
  rw [dist_comm] at h₂
  linarith
lemma contE (h : Fields.Euclidean S) (i : Future F a) : Continuous fun (t : ℝ≥0) => X.plant (travel i t) := by
  have he : Continuous fun (t : ℝ≥0) => kernel S a i.val (travel i t).val := by
    let c : E4 → ℂ := fun x => pointMoment S (reflect i.val a ++ carry i.val x)
    let f : ℝ≥0 → E4 := fun t => (t:ℝ) • basis a
    have h₁ : Continuous f := continuous_subtype_val.smul continuous_const
    have hu := (correl h a i i).1.comp_continuous h₁ (fun t => show 0 ≤ f t a by simp [f])
    exact hu
  apply continuous_iff_continuousAt.mpr
  intro t
  apply OS.ketC (D := X.H)
  · simp_rw [X.measure, sym_time h, advances]
    exact (he.comp (show Continuous (fun x : ℝ≥0 => x+x) from continuous_id.add continuous_id)).continuousAt
  simp_rw [X.measure,sym_time h a i, advances]
  exact (he.comp (show Continuous (fun x : ℝ≥0 => x+t) from continuous_id.add continuous_const)).continuousAt

lemma contU (h : Fields.Euclidean S) (i : Future F a) : Continuous fun (x : Cross a) => X.plant (over i x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply OS.ketC (D := X.H)
  · simp_rw [X.measure,sym_space h]; exact continuousAt_const
  simp_rw [X.measure]
  let F (x : Cross a) := (x.val : E4)
  have he : Continuous F := continuous_subtype_val
  have H := (correl h a (over i t) i).1.comp_continuous he (fun x => show _ from (le_of_eq x.property.symm))
  exact H.continuousAt

structure Chamber (S : F.Kernel) (a : Axis) where
  GNS : Schwinger S a
  flow : OS.Semigroup GNS.H a
  atBirth t (v : Future F a) : GNS.plant (travel v t) = flow.E t (GNS.plant v)
  across t (v : Future F a) : GNS.plant (over v t) = flow.U t (GNS.plant v)

lemma implement (H : Fields.Euclidean S) : ∃ C : Chamber S a, C.GNS = X := by
  choose E hE hP using fun (t : ℝ≥0) => X.by_bound (fun v => X.plant (travel v t)) 1 zero_le_one (by
    intro g; rw [one_mul]; exact contract X H t g)
  choose U hU hW using fun (x : Cross a) => X.by_bound (fun v => X.plant (over v x)) 1 zero_le_one (by
    intro g; rw [one_mul]; exact (safe X x H g).le)
  have es t : (E t).adjoint=E t := by
    apply X.by_bud; intro v
    refine X.whole.eq_of_inner_left ℂ fun f => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    -- linearity on all sums; compare singles
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => -- extract v form after adj rewrite
      simp only [map_add, inner_add_right,hf,hg]
    | single i c =>
      simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul,
        inner_smul_right,hP,X.measure,sym_time H]
  have hu : U 0=ContinuousLinearMap.id ℂ X.H := X.by_bud fun i => by rw [hW,pause]; rfl
  have hv (x y) : U (x+y)=(U x).comp (U y) := by
    apply X.by_bud; intro i; simp [hW, parallel, add_comm x y]
  let B : OS.Semigroup X.H a := {
    E := E
    U := U
    eZero := X.by_bud fun i => by rw [hP,done]; rfl
    sym := es
    uZero := hu
    space := hv
    shrinks := hE
    time := fun x y => X.by_bud fun i => by simp [hP,add_comm x y]
    independent := fun t y => X.by_bud fun i => by simp [hP,hW]
    unitary := by
      intro t p
      have ht (t : Cross a) (p) : ‖U t p‖ ≤ ‖p‖ := ((U t).le_opNorm p).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hU _))
      refine le_antisymm (ht _ _) ?_
      have he := ht (-t) (U t p)
      rw [← ContinuousLinearMap.comp_apply,← hv,neg_add_cancel,hu] at he
      exact he
    continuousE := strong X (D := X.H) hE fun i => by simp_rw [hP]; exact contE X H i
    continuousU := strong X (D := X.H) hU fun i => by simp_rw [hW]; exact contU X H i
  }
  exact ⟨⟨X,B,fun t v => (hP t v).symm,fun x v => (hW x v).symm⟩,rfl⟩

lemma realization {a : Axis} (H : Fields.Euclidean S) (h : Involutive (F.adj a)) : Nonempty (Chamber S a) :=
  ⟨(implement (Classical.choice (schwinger_ready H h)) H).choose⟩
end YM.Massive.Bridge
