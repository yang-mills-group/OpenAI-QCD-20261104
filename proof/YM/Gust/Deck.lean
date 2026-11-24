import YM.Gust.Sheer
-- Work.A01 and Push.Annular cutoff calculations adapted. -
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Table Work.A01 Analysis Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open Tarn Tarn.Choir
variable {Q : Choir} {n d:ℕ}
  {χ ψ:E4 → ℝ} {x:Points (n+1)}
def termG (J : Axis→Axis→ Q.W)(χ:E4→ℝ)(V:E4→E4)(x:Points n)(q:Fin n→ Q.W)(a b:Axis)(y:E4):=
    ((D (basis a) χ y * V y b : ℝ) : ℂ) * Q.total _ (Points.cons y x) (Fin.cons (J a b) q)
def fluxG (J : Axis→Axis→ Q.W) (χ:E4 → ℝ) (V:E4→E4)(x:Points n)(q:Fin n→ Q.W):=
    -∑ a : Axis, ∑ b : Axis, ∫ y:E4, termG J χ V x q a b y
abbrev about (J : Axis→Axis→ Q.W) (χ:E4→ℝ)(V:E4→E4)(x:Points (n+1)):= fluxG J χ (fun y=> V (y-x 0)) x
lemma termG_integrable (J : Axis → Axis → Q.W) (χ : E4 → ℝ) (V:E4 → E4) (x:Points (n+1)) (q:Fin (n+1) → Q.W) (h:Q.Domestic) (hx:x∈conf _) (hw:Window x χ) (a b:Axis) (hV:Continuous fun y=>V y b): Integrable (termG J χ V x q a b) := by
  have he:{y:E4|y ∈ tsupport (D (basis a) χ)} ⊆ {y:E4|y∈ tsupport (fderiv ℝ χ)}:=by
    apply closure_minimal ?_ (isClosed_tsupport _)
    exact fun y hy=> subset_tsupport _ (show fderiv ℝ χ y ≠0 from fun H=> hy (by simp [D,H]))
  have ht:Continuous (D (basis a) χ):=(hw.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχ:HasCompactSupport (D (basis a) χ):= hw.2.1.fderiv_apply ℝ _
  change Integrable fun y=> termG _ _ _ _ _ _ _ y
  simpa only [termG,Complex.real_smul, Complex.ofReal_mul, Pi.smul_apply,mul_assoc] using (cutoff_integrable (g:=fun y=> V y b • Q.total _ (Points.cons y x) (Fin.cons (J a b) q)) hχ ht (fun y hy=> hV.continuousAt (x:=y) |>.smul ((smooth_cons_ Q h (J a b) q (window_separated hx hw (he hy))).continuousAt)))
lemma expanded {J : Axis→Axis→ Q.W} {V : E4 → E4} (hx : x∈conf _) (hw : Window x χ) (h : Q.Domestic) (q : Fin (n+1) → Q.W)
    (hv : ∀ b : Axis, Continuous fun y => V y b) (a : Axis) :
    Integrable (fun y => D (basis a) χ y • currentG J V x q a y) ∧
    ∑ b : Axis, ∫ y, termG J χ V x q a b y = ∫ y, D (basis a) χ y • currentG J V x q a y := by
  have he (y) : D (basis a) χ y • currentG J V x q a y = ∑ b, termG J χ V x q a b y := by
    simp only [termG,currentG,Complex.ofReal_mul,Complex.real_smul,Finset.mul_sum,mul_assoc]
  simp_rw [he]
  have ht b := termG_integrable J χ V x q h hx hw a b (hv b)
  exact ⟨integrable_finsetSum _ fun i _ => ht i,(integral_finsetSum _ fun i _ => ht i).symm⟩

lemma independent (hs : Q.Domestic) {J : Axis→Axis→ Q.W} (hJ : Safe Q J)
    (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hk : killing V)
    (hx : x∈conf _) (hw : Window x χ) (ht : Window x ψ) (q : Fin (n+1) → Q.W) :
    fluxG J χ V x q = fluxG J ψ V x q := by
  have he := Gust.cutoff_zero hs J hJ V hv hk x q (χ-ψ) (hw.1.sub ht.1) (hw.2.1.sub ht.2.1) (StressFlux.Annular.difference_window hx hw ht)
  let F := currentG J V x q
  change -(∑ a, ∫ y, D (basis a) (χ-ψ) y • F a y)=0 at he
  have hc (y : E4) (a : Axis) : D (basis a) (χ-ψ) y • F a y = D (basis a) χ y • F a y - D (basis a) ψ y • F a y := by
    simp only [D,fderiv_sub ((hw.1.differentiable (by simp)) y) ((ht.1.differentiable (by simp)) y),_root_.sub_apply,sub_smul]
  have hp a := expanded (J:=J) hx hw hs q (fun b => (hv b).continuous) a
  have hr a := expanded (J:=J) hx ht hs q (fun b => (hv b).continuous) a
  simp_rw [hc] at he
  have hu a : (∫ y, (D (basis a) χ y • F a y - D (basis a) ψ y • F a y)) = (∑ b, ∫ y, termG J χ V x q a b y) - ∑ b, ∫ y, termG J ψ V x q a b y := by
    rw [integral_sub (hp a).1 (hr a).1, (hp a).2,(hr a).2]
  simp_rw [hu] at he
  rw [Finset.sum_sub_distrib, neg_eq_zero, sub_eq_zero] at he
  exact congr_arg Neg.neg he

variable {C:Sequence}{P:Calibration C}{T:Pollens P Q}
lemma moved (J : Axis→Axis→ Q.W) (V : E4 → E4) (c : E4) (ht : Foil P Q T) (hx : x∈conf _) (hw : Window x χ) (q : Fin (n+1) → Q.W) :
    about J (fun y => χ (y-c)) V (Points.across c x) q = about J χ V x q := by
  have he a b y : termG J (fun y => χ (y-c)) (fun y => V (y-Points.across c x 0)) (Points.across c x) q a b (y+c) =
      termG J χ (fun y => V (y-x 0)) x q a b y := by
    have hc : D (basis a) (fun y => χ (y-c)) (y+c) = D (basis a) χ y := by rw [D,show (fun y => χ (y-c)) = (fun y => χ (y + -c)) by simp only [sub_eq_add_neg], fderiv_comp_add_right (-c),← sub_eq_add_neg,add_sub_cancel_right,D]
    unfold termG
    simp only [hc,Points.across_coord, add_sub_add_right_eq_sub, StressFlux.Annular.across_cons]
    by_cases hz : D (basis a) χ y = 0
    · simp [hz]
    rw [ht.translation _ _ (separated_of_D hx hw hz)]
  have hi a b := integral_add_right_eq_self (termG J (fun y => χ (y-c)) (fun y => V (y-Points.across c x 0)) (Points.across c x) q a b) c (μ:=volume)
  simp_rw [he] at hi
  simp only [about,fluxG,hi]

end YM.Massive.Gust
#print axioms YM.Massive.Gust.independent
#print axioms YM.Massive.Gust.moved
