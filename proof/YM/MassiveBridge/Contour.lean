import YM.MassiveBridge.Region
import YM.Massive.Target.Statement
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import YM.Analysis.Polydisc
/-!
# A first Continuation clause of Goal without spin complexification

We need the exact `𝓝[east n]` convergence required by the target, not a chosen
profile. As for YM.Boundary.Waves we get this by real-height Taylor expansion of
the integrated functions, transferring time derivatives to Schwartz tests. Reuse
proofs from YM/{Shift/{Ridge,Breath,Osc},Work/C04}.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Filter Set Function MeasureTheory
open Boundary hiding Fields Surface Waves Small
open Boundary.Waves (clock)
open Probe LineDeriv Complex
open scoped Topology NNReal BigOperators InnerProductSpace ContDiff Interval ENNReal
variable {X : Fields} {S : X.Kernel} {F : Waves X} {C : Chamber S timeAxis} {n : ℕ}
structure Surface (X : Massive.Fields) where
  W (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => X.W) (Distn (Points n))
namespace Waves
section
variable (F : Waves X)
structure NonTangentialFree (B : Surface X) : Prop where
  int (n : ℕ) (v : Fin n → X.W) (y : Heights n) (h : y ∈ east n) (f : Joint n) :
    Integrable (fun x => F.restricted v y x * f x)
  corner (n : ℕ) (v : Fin n → X.W) (f : Joint n) :
    Tendsto (fun u => ∫ x, F.restricted v u x*f x) (𝓝[east n] (0:Heights n)) (𝓝 (B.W n v f))
-- integrate on the strict contour
def psi (v : Fin n → X.W) (y : Heights n) (f : Joint n) :=
    ∫ x, F.restricted v y x * f x
def Lines : Prop := ∀ n (v : Fin n → X.W) (f : Joint n) (y a : Heights n) (i : ℝ), y+i • a∈east n →
    HasDerivAt (fun t : ℝ => F.psi v (y+t • a) f) (F.psi v (y+i • a) (clock a f)) i

def Bounds : Prop := ∀ n (v : Fin n → X.W) (y : Heights n) (hy : y∈east n) (f : Joint n),
    Integrable (fun x => F.restricted v y x * f x)

def Along : Prop := ∀ n (v : Fin n → X.W) f, ContinuousOn (fun y => F.psi v y f) (east n)

variable {v : Fin n → X.W}
lemma beam (m : ℕ) (C : ℝ) (p : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x,
    ‖F.restricted v y x‖ ≤ C*k⁻¹^m) {y : Heights n} (h : y∈sunrise n) (f : Joint n) {k : ℝ} (hh : k ∈ Ioc 0 1) :
    k^m*‖F.psi v (y+k • rate n) f‖ ≤ C * weight f := by
  have he := hh.1
  refine (mul_le_mul_of_nonneg_left (compromise f _ _ (p _ _ hh (begins h _ hh.1.le))) (pow_nonneg he.le m)).trans_eq ?_
  rw [← mul_assoc, mul_left_comm, ← mul_pow,mul_inv_cancel₀ he.ne',one_pow,mul_one]
end
variable {y : Heights n}
open Metric
/-- Strict ordering gives a uniform positive clearance even on a neighbourhood
(not restricted to heights approaching on fixed rays). Subtract along `rate`, so
no need to take a min or choose a pair of indices; covers `n=0,1` too. -/
lemma room (hy : y ∈ east n) : ∃ k ∈ Ioc (0:ℝ) 1, ∀ᶠ u in 𝓝 y, broad u k := by
  have hc : Continuous (fun k : ℝ => y - k • rate n) := by fun_prop
  have ht : Tendsto (fun k : ℝ => y - k • rate n) (𝓝[>] 0) (𝓝 y) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ k in 𝓝[>] (0:ℝ), y - k • rate n ∈ east n :=
    ht.eventually ((open_east _).mem_nhds hy)
  obtain ⟨k, hr, hk⟩ := (he.and (show ∀ᶠ k in 𝓝[>] (0:ℝ), k ∈ Ioc 0 1 from
    Ioc_mem_nhdsGT zero_lt_one)).exists
  have hu : Continuous (fun u : Heights n => u - k • rate n) := by fun_prop
  refine ⟨k, hk, ?_⟩
  have hh : ∀ᶠ u in 𝓝 y, u - k • rate n ∈ east n :=
    (hu.tendsto y).eventually ((open_east _).mem_nhds hr)
  filter_upwards [hh] with u hu'
  simpa using begins (bigger hu') k hk.1.le

lemma bound_near (h : F.Breathes) (v : Fin n → X.W) (hy : y ∈ east n) :
    ∃ C : ℝ, ∀ᶠ u in 𝓝 y, ∀ p, ‖F.restricted v u p‖ ≤ C := by
  obtain ⟨k, hk, he⟩ := room hy
  obtain ⟨m, C, -, hC⟩ := h n v
  exact ⟨C*k⁻¹^m, he.mono (fun u hu => hC u k hk hu)⟩

lemma shift_strict (p : Points n) (hy : y ∈ east n) : shift p y ∈ strict n := by
  simpa using on_profile p y 1 zero_lt_one hy

lemma continuous_point (h : F.Region S) (v : Fin n → X.W) (hy : y ∈ east n) :
    Continuous (F.restricted v y) := by
  refine continuous_iff_continuousAt.mpr (fun p => ?_)
  let g := fun x : Points n => (shift x y, Boundary.trace x)
  have hg : Continuous g := by unfold g shift Boundary.trace time spatial; fun_prop
  have hs := (h.together n v).continuousAt
    (((open_strict n).prod isOpen_univ).mem_nhds
      (show g p ∈ strict n ×ˢ univ from ⟨shift_strict p hy, mem_univ _⟩))
  exact hs.comp hg.continuousAt

lemma continuous_height (h : F.Region S) (v : Fin n → X.W) (p : Points n)
    (hy : y ∈ east n) : ContinuousAt (fun u => F.restricted v u p) y := by
  let g := fun u : Heights n => (shift p u, Boundary.trace p)
  have hg : Continuous g := by
    have : Continuous (fun u : Heights n => shift p u) := by unfold shift; fun_prop
    exact this.prodMk continuous_const
  exact ((h.together n v).continuousAt
    (((open_strict n).prod isOpen_univ).mem_nhds
      (show g y ∈ strict n ×ˢ univ from ⟨shift_strict p hy, mem_univ _⟩))).comp hg.continuousAt

lemma bounds (h : F.Region S) (hb : F.Breathes) : F.Bounds := by
  intro n v y hy f
  obtain ⟨C, hC⟩ := bound_near hb v hy
  refine (f.integrable.norm.const_mul C).mono'
    (((continuous_point h v hy).mul f.continuous).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (mem_of_mem_nhds hC x) (norm_nonneg _)

lemma along (h : F.Region S) (hb : F.Breathes) : F.Along := by
  intro n v f y hy
  suffices ContinuousAt (fun u => F.psi v u f) y from this.continuousWithinAt
  obtain ⟨C, hC⟩ := bound_near hb v hy
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun u x => F.restricted v u x * f x)
    (bound := fun x => C*‖f x‖) ?_ ?_ (f.integrable.norm.const_mul C) ?_
  · filter_upwards [(open_east _).mem_nhds hy] with u hu
    exact (bounds h hb n v u hu f).aestronglyMeasurable
  · filter_upwards [hC] with u hu
    refine ae_of_all _ (fun x => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
  exact ae_of_all _ fun x => (continuous_height h v x hy).tendsto.mul tendsto_const_nhds

/-- Increasing the real-time coordinates along `a` corresponds to moving
in the real direction in this slice; increasing the heights along `a`
corresponds to moving in the positive imaginary direction. -/
def sliced (F : Waves X) (v : Fin n → X.W) (y a : Heights n)
    (p : Points n) (z : ℂ) : ℂ :=
  F.restricted v (y + z.im • a) (p + z.re • dawn a)

lemma moved (p : Points n) (y a : Heights n) (z : ℂ) :
    shift (p + z.re • dawn a) (y + z.im • a) = shift p y + z • (fun i => (a i : ℂ)) := by
  funext i
  apply Complex.ext <;> simp [shift, dawn, place, time, position]

lemma traced (p : Points n) (a : Heights n) (t : ℝ) :
    Boundary.trace (p + t • dawn a) = Boundary.trace p := by
  funext i
  apply PiLp.ext; intro j
  simp [Boundary.trace, spatial, dawn, place, position]

lemma diff_sliced (h : F.Region S) (v : Fin n → X.W) (p : Points n)
    (y a : Heights n) (z : ℂ) (hz : y + z.im • a ∈ east n) :
    DifferentiableAt ℂ (sliced F v y a p) z := by
  let l := fun w : ℂ => shift p y + w • (fun i => (a i : ℂ))
  have he : sliced F v y a p = (fun w => F.F n w (Boundary.trace p) v) ∘ l := by
    funext w
    rw [sliced, restricted, moved, traced]; rfl
  have hl : l z ∈ strict n := by
    unfold l; rw [← moved]; exact shift_strict _ hz
  rw [he]; exact ((h.hol n v _).differentiableAt ((open_strict _).mem_nhds hl)).comp z
    (show DifferentiableAt ℂ l z by unfold l; fun_prop)

lemma real_deriv (h : F.Region S) (v : Fin n → X.W) (p : Points n)
    (hy : y ∈ east n) (a : Heights n) :
    HasLineDerivAt ℝ (F.restricted v y) (deriv (sliced F v y a p) 0) p (dawn a) := by
  have he := (diff_sliced h v p y a 0 (by simpa using hy)).hasDerivAt.scomp_of_eq 0
    (Complex.ofRealCLM.hasDerivAt (x:=0)) (by simp)
  simpa [HasLineDerivAt, Function.comp_def, sliced] using he

lemma cr_height (h : F.Region S) (v : Fin n → X.W) (p : Points n) (y a : Heights n)
    (i : ℝ) (hi : y + i • a ∈ east n) :
    HasDerivAt (fun t : ℝ => F.restricted v (y + t • a) p)
      (I * lineDeriv ℝ (F.restricted v (y + i • a)) p (dawn a)) i := by
  let l : ℝ → ℂ := fun t => (↑t - ↑i) * I
  let u := y + i • a
  have hh : sliced F v u a p ∘ l = fun t : ℝ => F.restricted v (y + t • a) p := by
    funext t
    simp [l, sliced, u, sub_smul]
  have hd : HasDerivAt l I i := by
    simpa [l] using! (((Complex.ofRealCLM.hasDerivAt (x:=i)).sub_const (i:ℂ)).mul_const I)
  have hs := (diff_sliced h v p u a 0 (by simpa using hi)).hasDerivAt
  rw [(real_deriv h v p hi a).lineDeriv, ← hh]
  exact hs.scomp_of_eq i hd (by simp [l])

lemma deriv_bound_near (h : F.Region S) (hb : F.Breathes) (v : Fin n → X.W)
    (hy : y ∈ east n) (a : Heights n) :
    ∃ K : ℝ, ∀ᶠ u in 𝓝 y, ∀ p,
      ‖lineDeriv ℝ (F.restricted v u) p (dawn a)‖ ≤ K := by
  obtain ⟨C, hC⟩ := bound_near hb v hy
  let l := fun q : Heights n × ℂ => q.1 + q.2.im • a
  have hc : Continuous l := by unfold l; fun_prop
  have ht : Tendsto l (𝓝 (y,0)) (𝓝 y) := by simpa [l] using hc.tendsto (y,0)
  have he : {q : Heights n × ℂ | l q ∈ east n ∧ ∀ p, ‖F.restricted v (l q) p‖ ≤ C}
      ∈ 𝓝 (y,0) := ht.eventually ((show ∀ᶠ u in 𝓝 y, u ∈ east n from
        (open_east _).mem_nhds hy).and hC)
  rw [nhds_prod_eq] at he
  obtain ⟨s, hs, t, ht', H⟩ := Filter.mem_prod_iff.1 he
  obtain ⟨r, hr, hr'⟩ := nhds_basis_closedBall.mem_iff.1 ht'
  refine ⟨C / r, ?_⟩
  filter_upwards [hs] with u hu p
  have hd z (hz : z ∈ closedBall (0:ℂ) r) :
      u + z.im • a ∈ east n ∧ ‖sliced F v u a p z‖ ≤ C := by
    have he' := H (show (u,z) ∈ s ×ˢ t from ⟨hu,hr' hz⟩)
    exact ⟨he'.1,he'.2 _⟩
  have hu' : u ∈ east n := by simpa using (hd 0 (mem_closedBall_self hr.le)).1
  have hc' : DifferentiableOn ℂ (sliced F v u a p) (closedBall (0:ℂ) r) :=
    fun z hz => (diff_sliced h v p u a z (hd z hz).1).differentiableWithinAt
  rw [(real_deriv h v p hu' a).lineDeriv]
  exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hc'.diffContOnCl_ball subset_rfl)
    (fun z hz => (hd z (sphere_subset_closedBall hz)).2)

lemma lines (h : F.Region S) (hb : F.Breathes) : F.Lines := by
  intro n v f y a i hi
  let l : ℝ → Heights n := fun t => y + t • a
  let g := fun (t : ℝ) => F.restricted v (l t)
  let d := fun (t : ℝ) (x : Points n) => lineDeriv ℝ (g t) x (dawn a)
  have hl : l i ∈ east n := hi
  obtain ⟨K, hK⟩ := deriv_bound_near h hb v hl a
  let s := {t : ℝ | l t ∈ east n ∧ ∀ x, ‖d t x‖ ≤ K}
  have hs : s ∈ 𝓝 i := ((show Continuous l by unfold l; fun_prop).tendsto i).eventually
    ((show ∀ᶠ u in 𝓝 (l i), u ∈ east n from (open_east _).mem_nhds hl).and hK)
  have hx : i ∈ s := mem_of_mem_nhds hs
  have he : Integrable (fun x => g i x * f x) := bounds h hb n v (l i) hi f
  have he' : Integrable (fun x => d i x * f x) := by
    refine (f.integrable.norm.const_mul K).mono' ((aestronglyMeasurable_lineDeriv
      (continuous_point h v hl) _).mul f.integrable.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hx.2 x) (norm_nonneg _)
  have H : HasDerivAt (fun t : ℝ => F.psi v (y + t • a) f)
      (∫ x, I * (d i x * f x)) i := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun t x => g t x * f x)
      (F' := fun t x => I * (d t x * f x)) hs ?_ he ((he'.const_mul I).aestronglyMeasurable) ?_
      (f.integrable.norm.const_mul K) ?_).2
    · filter_upwards [hs] with t ht
      exact (bounds h hb n v (l t) ht.1 f).aestronglyMeasurable
    · refine ae_of_all _ (fun x t ht => ?_)
      rw [norm_mul,norm_I,one_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (ht.2 x) (norm_nonneg _)
    refine ae_of_all _ (fun x t ht => ?_)
    exact ((cr_height h v x y a t ht.1).mul_const (f x)).congr_deriv (mul_assoc ..)
  let f' := ∂_{dawn a} f
  have hp : (∫ x, g i x * f' x) = -∫ x, d i x * f x :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℂ) (v := dawn a)
      (f := g i) (g := ⇑f) (f' := d i) (g' := ⇑f') he'
      (bounds h hb n v (l i) hi f') he
      (fun x _ => (real_deriv h v x hi a).lineDifferentiableAt.hasLineDerivAt)
      (fun x _ => (f.hasFDerivAt x).hasLineDerivAt _)
  apply H.congr_deriv
  calc
    _ = - I * ∫ x, g i x * f' x := by rw [integral_const_mul, hp]; ring
    _ = ∫ x, g i x * (Boundary.Waves.clock a f x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      change -I * (g i x * f' x) = g i x * (-I * f' x)
      ring
    _ = _ := rfl


variable (F : Waves X)


def moves : (k : ℕ) → Joint n →L[ℂ] Joint n
  | 0 => ContinuousLinearMap.id ℂ _
  | k+1 => (clock (rate n)).comp (moves k)

def rocks (v : Fin n → X.W) (y : Heights n) (f : Joint n) (t : ℝ) (k : ℕ) := F.psi v (y+t • rate n) (moves k f)

def coal (t : ℝ) (m : ℕ) := (-↑t : ℂ)^m*(m.factorial:ℂ)⁻¹

def pol (v : Fin n → X.W) (y : Heights n) (f : Joint n) (t : ℝ) (m : ℕ) :=
    ∑ k ∈ Finset.range (m+1), coal t k * F.rocks v y f t k

def wind (v : Fin n → X.W) (m : ℕ) (y : Heights n) (f : Joint n) (t : ℝ) := coal t m * F.rocks v y f t (m+1)

def desired (v : Fin n → X.W) (m : ℕ) (y : Heights n) (f : Joint n) := F.pol v y f 1 m -∫ s : ℝ in Ioc 0 1,
    F.wind v m y f s

private lemma pipe (t : ℝ) (m : ℕ) : HasDerivAt (fun t : ℝ => coal t (m+1)) (-coal t m) t := by
  have he := (Complex.ofRealCLM.hasDerivAt (x:=t)).neg.pow (m+1) |>.mul_const ((m+1).factorial:ℂ)⁻¹
  apply he.congr_deriv
  unfold coal
  have hp : (m.factorial:ℂ)≠0 := by norm_cast; exact Nat.factorial_ne_zero _
  have hv : (m:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv]
  push_cast; simp only [Pi.neg_apply, ofRealCLM_apply,ofReal_one]
  field_simp

lemma right (h : F.Lines) (v : Fin n → X.W) (y : Heights n) (f : Joint n) (m : ℕ) (x : ℝ)
    (p : y+x • rate n∈east n) : HasDerivAt (fun t => F.pol v y f t m) (F.wind v m y f x) x := by
  have H (k) : HasDerivAt (fun t => F.rocks v y f t k) (F.rocks v y f x (k+1)) x := h n v (moves k f) y _ x p
  induction m with
  | zero => simpa [wind,pol,coal] using! H 0
  | succ m IH =>
    have ht := IH.add ((pipe x m).mul (H (m+1)))
    simp_rw [show (fun t => F.pol v y f t (m+1))= (fun t => F.pol v y f t m+coal t (m+1)*F.rocks v y f t (m+1)) from funext fun t => Finset.sum_range_succ (fun k ↦ coal t k*_) _]
    apply ht.congr_deriv; unfold wind; ring

theorem meant (ha : F.Along) (h : F.Lines) (v : Fin n → X.W) (y : Heights n) (hy : y∈east n)
    (f : Joint n) (m : ℕ) : F.desired v m y f= F.psi v y f := by
  unfold desired
  have he (x : ℝ) (hx : x ∈ uIcc (0:ℝ) 1) : y+x • rate n∈east n := grows hy (by rw [uIcc_of_le zero_le_one] at hx; exact hx.1)
  have ht : F.pol v y f 0 m= F.psi v y f := by
    unfold pol
    rw [Finset.sum_eq_single_of_mem 0 (by simp)]
    · simp [coal,rocks,moves]
    intro b _ hb; simp [coal,zero_pow hb]
  rw [← intervalIntegral.integral_of_le (a:=(0:ℝ)) (b:=1) zero_le_one, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => F.right h v y f m x (he x hx)), ht]; swap
  · have hh : ContinuousOn (F.wind v m y f) (uIcc (0:ℝ) 1) := by
      unfold wind; apply ContinuousOn.mul
      · unfold coal; fun_prop
      exact (ha n v _).comp (show ContinuousOn (fun t : ℝ => y+t • rate n) _ from by fun_prop) he
    exact hh.intervalIntegrable
  abel

lemma expense {v : Fin n → X.W} (m : ℕ) {C : ℝ}
    (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)
    (y : Heights n) (hy : y∈sunrise n) (f : Joint n) {t : ℝ} (hr : t∈Ioc (0:ℝ) 1) :
    ‖F.wind v m y f t‖ ≤ C*weight (moves (m+1) f) := by
  have hF : ‖(m.factorial:ℂ)‖ = (m.factorial:ℝ) := by exact Complex.norm_natCast _
  have he : ((m.factorial:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos m)
  rw [wind,norm_mul,coal,norm_mul, Complex.norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr.1.le, norm_inv,hF]
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg hr.1.le m) he) (norm_nonneg _))
    (beam F m C hm hy (moves (m+1) f) hr)

theorem maintains (v : Fin n → X.W) (ha : F.Along) (m : ℕ) {C : ℝ}
    (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)
    (f : Joint n) : ContinuousOn (fun y => F.desired v m y f) (sunrise n) := by
  intro s hs
  unfold desired
  apply ContinuousWithinAt.sub
  · apply ContinuousOn.continuousWithinAt (s:=sunrise n) (x:=s) (by
      unfold pol
      apply continuousOn_finsetSum; intro i _; apply ContinuousOn.const_mul
      exact (ha n v (moves _ f)).comp (continuous_id.add continuous_const).continuousOn (fun _ H => dawns H zero_lt_one)) hs
  refine tendsto_integral_filter_of_dominated_convergence (F:=fun (y : Heights n) => F.wind v m y f)
    (f:= F.wind v m s f) (bound := fun t : ℝ => C*weight (moves (m+1) f)) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have ht : ContinuousOn (F.wind v m y f) (Ioc 0 1) := by
      unfold wind; apply ContinuousOn.mul; unfold coal; fun_prop
      exact (ha n v _).comp (show ContinuousOn (fun t : ℝ => y+t • rate n) _ from by fun_prop) (fun _ p => dawns hy p.1)
    exact ht.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x h => F.expense m hm _ hy f h
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro x hx
  have H : ContinuousOn (fun y : Heights n => F.psi v (y+x • rate n) (moves (m+1) f)) (sunrise n) :=
    (ha n v _).comp (continuous_id.add continuous_const).continuousOn (fun _ hy => dawns hy hx.1)
  exact tendsto_const_nhds.mul (H s hs)


section price
variable {v : Fin n → X.W} {C : ℝ} {m : ℕ}
variable (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)

def toll (f : Joint n) (C : ℝ) (m : ℕ) := (∑ j ∈ Finset.range (m+1), ‖coal 1 j‖*(C*weight (moves j f)))+
    C*weight (moves (m+1) f)
lemma tolls (m : ℕ) (C : ℝ) : toll (0:Joint n) C m=0 ∧ Continuous fun f : Joint n => toll f C m := by
  unfold toll
  refine ⟨by simp,?_⟩
  apply Continuous.add
  · apply continuous_finsetSum; intro j _; exact Continuous.const_mul (Continuous.const_mul (weight_cont.comp (moves j).continuous) C) _
  exact Continuous.const_mul (weight_cont.comp (moves (m+1)).continuous) _

include hm
lemma cost (y) (hy : y∈sunrise n) (f : Joint n) : ‖F.desired v m y f‖ ≤ toll f C m := by
  unfold desired toll
  refine (norm_sub_le ..).trans (add_le_add ?_ ?_)
  · unfold pol; apply (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => ?_)
    have he := beam F m C hm hy (moves j f) (show (1:ℝ)∈Ioc 0 1 from ⟨zero_lt_one,le_rfl⟩)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (by simpa only [rocks,one_pow,one_mul] using he) (norm_nonneg _)
  have hh := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0:ℝ) 1))
    (g := fun _ => C*weight (moves (m+1) f)) (f := F.wind v m y f) (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun _ hx => F.expense _ hm _ hy f hx)
  simpa using hh

lemma storm (h : F.Along) (p : F.Lines) (y) (hy : y∈sunrise n) (f : Joint n) : Tendsto (fun x => F.psi v x f)
    (𝓝[east n] y) (𝓝 (F.desired v m y f)) := by
  apply ((F.maintains v h _ hm f y hy).mono fun x t => bigger (n:=n) t).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx using F.meant h p _ _ hx f m
end price

lemma seeks (h : F.Bounds) (ha : F.Along) (hm : F.Lines) (hp : F.Breathes) (y) (hy : y∈sunrise n) :
    ∃ W : MultilinearMap ℂ (fun _ : Fin n => X.W) (Distn (Points n)), ∀ (v : Fin n → X.W) (f : Joint n),
    Tendsto (fun t => F.psi v t f) (𝓝[east n] y) (𝓝 (W v f)) := by
  classical
  let T := 𝓝[east n] y
  have hT : T.NeBot := awaits hy
  choose m C hC H using hp n
  let g (v : Fin n → X.W) := F.desired v (m v) y
  have hg v f : Tendsto (fun t => F.psi v t f) T (𝓝 (g v f)) := F.storm (H v) ha hm y hy f
  let D (v : Fin n → X.W) : Joint n→ₗ[ℂ] ℂ :=
    { toFun := g v
      map_add' := by
        intro f p; refine tendsto_nhds_unique (hg v (f+p)) (((hg v f).add (hg v p)).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi; rw [← integral_add (h n v t ht f) (h n v t ht p)]
        apply integral_congr_ae; filter_upwards with x; simp [mul_add]
      map_smul' := by
        intro c f; apply tendsto_nhds_unique (hg v (c•f)) (((hg v f).const_mul c).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi; rw [← integral_const_mul]; congr! 1; ext x; simp; ring }
  let W (v) : Distn (Points n) := ⟨D v, sways (fun f => toll f (C v) (m v)) (tolls (m v) (C v)).2 (tolls (m v) (C v)).1 (fun f => F.cost (H v) y hy f)⟩
  let B : MultilinearMap ℂ (fun _ : Fin n => X.W) (Distn (Points n)) :=
    { toFun := W
      map_update_add' := by
        intro _ v j x z; ext1 f
        refine tendsto_nhds_unique (hg (update v j (x+z)) f) (((hg (update v j x) f).add (hg (update v j z) f)).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi
        rw [← integral_add (h n _ t ht _) (h n _ t ht _)]
        congr! 1; ext p; simp [restricted,add_mul]
      map_update_smul' := by
        intro _ v j c x; ext1 f
        refine tendsto_nhds_unique (hg (update v j (c•x)) f) (((hg (update v j x) f).const_mul c).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi
        rw [← integral_const_mul]; congr! 1; ext p; simp [restricted,mul_assoc] }
  exact ⟨B,hg⟩

/-- All ordered heights, *not just fixed slopes*, as required for Hilbert vector limits. -/
lemma jointly (h : F.Bounds) (ha : F.Along) (hm : F.Lines) (hp : F.Breathes) :
    ∃ W : Surface X, F.NonTangentialFree W := by
  choose B hB using fun n : ℕ => F.seeks h ha hm hp 0 (light n)
  exact ⟨⟨B⟩,⟨h,hB⟩⟩

def system (W : Surface X) : Continuation X := ⟨W.W,F.F⟩
lemma produces (W : Surface X) (H : F.Region S) (hx : F.NonTangentialFree W) : (F.system W).Produces S :=
  ⟨H.together,H.hol,H.roots,fun n y h f v=>hx.int n v y h f,fun n f v=>hx.corner n v f⟩
end Waves
lemma opens (E : Fields.Euclidean S) (full : ∀ x : X.W, ∃ D, x∈X.level D) (A : Spread C) :
    ∃ (B : MatrixCap C) (F : Waves X) (W : Surface X), B.concretized A ∧ (∀ v, B.rated v) ∧ B.Defined F ∧ F.Region S ∧ F.Breathes ∧
    F.NonTangentialFree W := by
  obtain ⟨B,hB,hx⟩:=MatrixCap.affordable E full A
  obtain ⟨F,hF⟩:=B.defined_exists hB
  have ht:=B.defined_region E hB hF
  have hp:= B.defined_power hx hF
  obtain ⟨W,hW⟩:= Waves.jointly F (Waves.bounds ht hp) (Waves.along ht hp) (Waves.lines ht hp) hp
  exact ⟨B,F,W,hB,hx,hF,ht,hp,hW⟩

/-- Answer the ensemble-contour requirement at any S satisfying the earlier `TheoryAt` clauses. -/
lemma continuation {R : Massive.Sequence} {P : Calibration R} (e : X.System P) (H : Fields.Euclidean S) : ∃ w : Continuation X, w.Produces S := by
  obtain ⟨C⟩:=realization H (e.reflected timeAxis)
  obtain ⟨A⟩:=spread_ready C H e.increases e.exhaustive
  obtain ⟨B,F,W,-,-,-,h,-,hp⟩:=opens H e.exhaustive A
  exact ⟨F.system W,F.produces W h hp⟩
#print axioms continuation
end YM.Massive.Bridge
