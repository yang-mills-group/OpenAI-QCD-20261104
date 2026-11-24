import YM.Push.STRESS_FLUX.Annular
import YM.Mistral.Tails
import YM.Roan.Peak
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 880000
namespace YM.Massive.Gust
open Analysis Function Set Filter MeasureTheory Tarn Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
open Tarn.Choir Work.A01
variable {Q:Choir} {n d : ℕ}
/-- Annular methods of Work.A01, adapted to the pre-System: same Choir and separated laws. -/
structure Safe (K:Choir)(T:Axis → Axis→ K.W) :Prop where
    symmetric a b:T a b=T b a
    divergence b:∑ a:Axis, K.arc a (T a b)=0
noncomputable def headG (q:Fin n→ Q.W)(p:Points (n+1)): Q.W→ₗ[ℂ]ℂ:= (Q.total (n+1) p).toLinearMap (Fin.cons 0 q) 0
theorem heads (q:Fin n→ Q.W)(p:Points (n+1))(x:Q.W): headG q p x=Q.total _ p (Fin.cons x q):=by apply congr_arg (Q.total _ p); ext1 i; cases i using Fin.cases <;> simp
theorem smooth_cons_ (Q: Choir) (h:Q.Domestic) (v : Q.W) {x : Points n} (q : Fin n → Q.W)
    {y : E4} (hy : Points.cons y x ∈ conf _) :
    ContDiffAt ℝ ∞ (fun z => Q.total _ (Points.cons z x) (Fin.cons v q)) y := by
  have hu : ContDiff ℝ ∞ (fun p => Points.cons p x) := by
    rw [shifting_head]; exact (Work.A01.headDir n).contDiff.add contDiff_const
  exact (((h.smooth _ _ _ hy).contDiffAt ((conf_open _).mem_nhds hy))).comp y hu.contDiffAt

theorem D_cons_ (h : Q.Domestic) (v : Q.W)
    {x : Points n} (q : Fin n → Q.W) {y : E4} (hy : Points.cons y x ∈ conf _) (a : Axis) :
    D (basis a) (fun p => Q.total _ (Points.cons p x) (Fin.cons v q)) y =
      Q.total _ (Points.cons y x) (Fin.cons (Q.arc a v) q) := by
  let F := fun p : Points (n+1) => Q.total _ p (Fin.cons v q)
  let u := fun p => Points.cons p x
  have hu : HasFDerivAt u (Work.A01.headDir n) y := by
    unfold u; rw [shifting_head]
    exact (Work.A01.headDir n).hasFDerivAt.add_const _
  have he : DifferentiableAt ℝ F (u y) :=
    ((h.smooth _ _ _ hy).contDiffAt ((conf_open _).mem_nhds hy)).differentiableAt (by simp)
  change fderiv ℝ (F ∘ u) y (basis a) = _
  haveI : ContinuousSMul ℝ (Points (n+1)):=IsBoundedSMul.continuousSMul
  have hv : fderiv ℝ u y = Work.A01.headDir n:= by exact hu.fderiv
  rw [fderiv_comp y he hu.differentiableAt, hv, ContinuousLinearMap.comp_apply,
    show Work.A01.headDir n (basis a) = Points.direction 0 a from ?_]
  · refine Eq.trans (h.derivatives _ _ hy (Fin.cons v q) 0 a) (congr_arg (Q.total _ (u y)) ?_)
    ext1 i; cases i using Fin.cases <;> simp
  · ext1 i; change Points.cons (basis a) 0 i = _
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons, Points.direction]

/-- V contracts the second index. The fixed x,q are arbitrary (here used
for the actual exterior insertions after deleting the unit). -/
def currentG (J : Axis → Axis → Q.W) (V : E4 → E4) (x : Points n) (q : Fin n → Q.W) (a : Axis) (y : E4) :=
  ∑ b : Axis, V y b • Q.total _ (Points.cons y x) (Fin.cons (J a b) q)

theorem smooth_currentG (J : Axis → Axis → Q.W) (V : E4 → E4) {x : Points n} (q : Fin n → Q.W) (a : Axis)
    {y : E4} (hV : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hy : Points.cons y x ∈ conf _)
    (hs : Q.Domestic) : ContDiffAt ℝ ∞ (currentG J V x q a) y := by
  change ContDiffAt ℝ ∞ (fun _ => ∑ _, _) _
  exact ContDiffAt.sum fun b _ => (hV b).contDiffAt.smul (smooth_cons_ Q hs _ q hy)

theorem divergence (hs : Q.Domestic)
    (J : Axis → Axis → Q.W) (hJ : Safe Q J) (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b))
    (hk : killing V) {x : Points n} (q : Fin n → Q.W) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (currentG J V x q a) y = 0 := by
  let F (a b : Axis) (p : E4) := Q.total _ (Points.cons p x) (Fin.cons (J a b) q)
  let T a b := D (basis a) (fun z => V z b) y • F a b y
  let R (a b : Axis) := V y b • Q.total _ (Points.cons y x)
    (Fin.cons (Q.arc a (J a b)) q)
  have hf (a b : Axis) : DifferentiableAt ℝ (F a b) y :=
    (smooth_cons_ Q hs _ q hy).differentiableAt (by simp)
  have hp (b : Axis) : DifferentiableAt ℝ (fun z => V z b) y := (hv b).differentiable (by simp) y
  have he (a b : Axis) : D (basis a) (fun z => V z b • F a b z) y = T a b + R a b := by
    calc
      _ = D (basis a) (fun z => V z b) y • F a b y + V y b • D (basis a) (F a b) y := by
        unfold D; rw [fderiv_fun_smul (hp b) (hf a b)]; simp [add_comm]
      _ = _ := by
        change _ + V y b • D (basis a) (fun z => F a b z) y = _
        unfold F
        rw [D_cons_ hs _ q hy a]
  have hi (a : Axis) : D (basis a) (currentG J V x q a) y = ∑ b : Axis, (T a b + R a b) := by
    change fderiv ℝ (fun z => ∑ b : Axis, V z b • F a b z) y _ = _
    rw [fderiv_fun_sum fun b _ => (show DifferentiableAt ℝ (fun z => V z b • F a b z) y from
        (hp b).smul (hf a b)), _root_.sum_apply]
    exact Finset.sum_congr rfl fun b _ => he a b
  simp_rw [hi, Finset.sum_add_distrib]
  have ht : ∑ a, ∑ b, R a b = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero
    intro b _
    simp_rw [R, ← heads, ← Finset.smul_sum, ← map_sum, hJ.divergence, map_zero, smul_zero]
  have ha : ∀ a b, T a b = -T b a := by
    intro a b; unfold T; rw [hk, neg_smul, show F a b y = F b a y from by unfold F; rw [hJ.symmetric a b]]
  let z := ∑ a, ∑ b, T a b
  have hh : z = -z := calc
    z = ∑ b, ∑ a, (-T a b) := by
      apply Finset.sum_congr rfl; intro a _
      exact Finset.sum_congr rfl fun b _ => ha a b
    _ = -(∑ b, ∑ a, T a b) := by simp_rw [Finset.sum_neg_distrib]
    _ = -z := by rw [Finset.sum_comm]
  have hh' : (2:ℂ)*z = 0 := by
    rw [two_mul]; conv_lhs => lhs; rw [hh]
    exact neg_add_cancel z
  rw [ht,add_zero]; exact (mul_eq_zero.mp hh').resolve_left (by norm_num)

/-- Integration by parts against the compactly supported cutoff χ, away
from the points of the word. No conditions at infinity on the readout. -/
theorem cutoff_zero (hs : Q.Domestic)
    (J : Axis → Axis → Q.W) (hJ : Safe Q J) (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b))
    (hk : killing V) (x : Points n) (q : Fin n → Q.W) (χ : E4 → ℝ) (hw : ContDiff ℝ ∞ χ)
    (hχ : HasCompactSupport χ) (hp : ∀ y ∈ tsupport χ, Points.cons y x ∈ conf _) :
    - (∑ a : Axis, ∫ y : E4, D (basis a) χ y • currentG J V x q a y) = 0 := by
  let F := currentG J V x q
  have hF (a : Axis) (y) (hy : y ∈ tsupport χ) : ContDiffAt ℝ ∞ (F a) y :=
    smooth_currentG J V q a hv (hp y hy) hs
  have h1 (a : Axis) : Integrable fun y => D (basis a) χ y • F a y := by
    refine cutoff_integrable (hχ.fderiv_apply ℝ (basis a)) ?_ ?_
    · exact continuous_iff_continuousAt.mpr (fun y =>
        (dSmooth (m:=∞) (hw.contDiffAt (x:=y)) (basis a) (by simp)).continuousAt)
    · exact fun y hy => (hF a y (tsupport_fderiv_apply_subset ℝ _ hy)).continuousAt
  have h2 (a : Axis) : Integrable fun y => χ y • D (basis a) (F a) y := cutoff_integrable hχ hw.continuous
    (fun y hy => (dSmooth (m:=∞) (hF a y hy) _ (by simp)).continuousAt)
  have he (a : Axis) : (∫ y, χ y • D (basis a) (F a) y) = -∫ y, D (basis a) χ y • F a y :=
    integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (h1 a) (h2 a)
      (cutoff_integrable hχ hw.continuous (fun y hy => (hF a y hy).continuousAt))
      (fun y _ => hw.differentiable (by simp) y) (fun y hy => (hF a y hy).differentiableAt (by simp))
  have ht (y : E4) : (∑ a, χ y • D (basis a) (F a) y) = 0 := by
    by_cases hx : y ∈ tsupport χ
    · rw [← Finset.smul_sum, divergence hs J hJ V hv hk q (hp y hx), smul_zero]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  change -(∑ a, ∫ y, D (basis a) χ y • F a y) = 0
  rw [← Finset.sum_neg_distrib]
  simp_rw [← he]
  rw [← integral_finsetSum _ (fun a _ => h2 a)]
  simp_rw [ht]; simp

end YM.Massive.Gust
#print axioms YM.Massive.Gust.cutoff_zero
