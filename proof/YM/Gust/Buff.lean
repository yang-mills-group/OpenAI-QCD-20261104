import YM.Push.STRESS_FLUX.Scaling
import YM.Gust.Deck
set_option maxHeartbeats 650000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Analysis Function Set Filter MeasureTheory Table Work.A05 Tarn Tarn.Choir
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {Q:Choir}{C: Sequence}{P:Calibration C}{r:ℝ}{V:E4→E4}{i:ℕ}
abbrev xP (s:Patrol P):Points (s.size+1):= points (Fin.cons 0 s.land)
lemma hereP (s:Patrol P) : xP s 0=0:=rfl
abbrev wordsP(K:Choir)(s:Patrol P): Fin s.size → K.W:=fun i=> K.focus none (s.stars i) (s.texts i)
def boostL : ContDiffBump (0:E4) := ⟨1,2,by norm_num,by norm_num⟩

lemma weight_off (a : Axis) (b : E4 → ℝ) {z : E4} (hz : Work.A05.weight boostL a b z ≠ 0) : 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 := by
  have he : z ∈ tsupport (fderiv ℝ (boostL : E4 → ℝ)) := subset_closure (show fderiv ℝ (boostL : E4 → ℝ) z ≠ 0 from fun h => hz (by simp [Work.A05.weight,Analysis.D,h]))
  have ht := tsupport_fderiv_subset ℝ he; rw [boostL.tsupport_eq] at ht
  refine ⟨?_, by simpa [Metric.mem_closedBall,dist_zero_right,boostL] using ht⟩
  by_contra! h
  apply notMem_tsupport_iff_eventuallyEq.mpr _ he
  have hz : z∈ Metric.ball (0:E4) boostL.rIn := by simp only [Metric.mem_ball,dist_zero_right,boostL]; linarith
  have hh : (boostL : E4 → ℝ) =ᶠ[𝓝 z] fun _ => 1 := (Metric.isOpen_ball.eventually_mem hz).mono fun _ hu => boostL.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
  simpa using hh.fderiv (𝕜:=ℝ)

lemma eventual_stretch (s : Patrol P) {e : ℕ → ℝ} (hp : ∀ᶠ k in atTop, 0 < e k) (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ k : ℕ in atTop, Window (xP s) (stretch (e k) boostL) := by
  have hu (i : Fin s.size) : ∀ᶠ k in atTop, ((e k)⁻¹ • (xP s)) i.succ ∉ tsupport (boostL : E4 → ℝ) := by
    have hr : 0 < ‖(xP s) i.succ‖ := norm_pos_iff.mpr (hereP s ▸ (show (xP s) i.succ ≠ (xP s) 0 from ((show Injective (xP s).ofLp from s.ok).ne (Fin.succ_ne_zero i))) : (xP s) i.succ ≠ 0)
    have ht:= (he.const_mul 2).eventually_lt_const (show 2*(0:ℝ)< ‖(xP s) i.succ‖ from by simpa using hr)
    filter_upwards [hp,ht] with k hp hk
    rw [boostL.tsupport_eq]; simp only [Metric.mem_closedBall,not_le,dist_zero_right,PiLp.smul_apply,norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp),boostL]
    exact (lt_inv_mul_iff₀ hp).mpr (by linarith only [hk])
  filter_upwards [hp,eventually_all.mpr hu] with k hp hk
  have ht := window_stretch (x:= (e k)⁻¹ • (xP s)) (χ:=boostL) hp ⟨boostL.contDiff, boostL.hasCompactSupport, by
    simp only [PiLp.smul_apply,hereP s,smul_zero]; exact boostL.eventuallyEq_one, hk⟩
  rwa [smul_inv_smul₀ hp.ne'] at ht

def parcel (J : Axis→Axis→ Q.W) (B : Q.W) (V : E4 → E4) (i : ℕ) (s : Patrol P) (r : ℝ) (a b : Axis) (z : E4) :=
  Work.A05.weight boostL a (fun z => V z b) z *
    ((r:ℂ)^(3+i) * Q.total _ (Points.cons (r • z) (xP s)) (Fin.cons (J a b) (Fin.cons B (wordsP Q s))))

lemma parcel_eq (J : Axis→Axis→ Q.W) (B : Q.W) (hv : StressFlux.Annular.Motion i V) (hr : 0<r) (s : Patrol P) (a b : Axis) (z : E4) :
    parcel J B V i s r a b z = (r:ℂ)^4 * termG J (stretch r boostL) (fun y => V (y-(xP s) 0)) (xP s) (Fin.cons B (wordsP Q s)) a b (r • z) := by
  simp only [parcel,termG,D_stretch hr boostL.contDiff,Work.A05.weight,hereP s,sub_zero,hv.scales r hr,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_pow, pow_add,Complex.ofReal_mul,Complex.ofReal_inv]
  have hz : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

lemma parcel_integrable (J : Axis→Axis→ Q.W) (B : Q.W) (hv : StressFlux.Annular.Motion i V) (hr : 0<r) (s : Patrol P) (hw : Window (xP s) (stretch r boostL)) (hs : Q.Domestic) (a b : Axis) :
    Integrable (parcel J B V i s r a b) := by
  change Integrable (fun y => parcel J B V i s r a b y)
  simp_rw [parcel_eq J B hv hr]
  exact ((termG_integrable J (stretch r boostL) _ _ (Fin.cons B _) hs (s.ok) hw a b ((hv.smooth b).continuous.comp (continuous_id.sub continuous_const))).comp_smul hr.ne').const_mul _

lemma scaled (J : Axis→Axis→ Q.W) (B : Q.W) (hv : StressFlux.Annular.Motion i V) (hr : 0<r) (s : Patrol P) :
    about J (stretch r boostL) V (xP s) (Fin.cons B (wordsP Q s)) = -∑ a, ∑ b, ∫ z, parcel J B V i s r a b z := by
  have ht (a b : Axis) := Measure.integral_comp_smul_of_nonneg volume (termG J (stretch r boostL) (fun y => V (y-(xP s) 0)) (xP s) (Fin.cons B (wordsP Q s)) a b) r (hR := hr.le)
  have hz : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp_rw [parcel_eq J B hv hr,integral_const_mul,ht,show Module.finrank ℝ E4 = 4 from finrank_euclideanSpace_fin,
    Complex.real_smul, Complex.ofReal_inv,Complex.ofReal_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hz)]
  rfl

def mass (V : E4 → E4) (a b : Axis) (z : E4) := ‖Work.A05.weight boostL a (fun z => V z b) z‖

end YM.Massive.Gust
#print axioms YM.Massive.Gust.scaled
#print axioms YM.Massive.Gust.parcel_integrable
#print axioms YM.Massive.Gust.eventual_stretch
