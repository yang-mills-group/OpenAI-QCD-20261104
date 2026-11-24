import YM.QCD.Step.Match
import YM.Work.F02.Series

/-! # local letters with all-link expansion. Crude bills, analytic in independent link and
inverse-link matrices. Evaluate scalar high determinant logs using real part on settled links. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Finset Function Filter Lat Wilson Lattice Cost Metric
open scoped Matrix Matrix.Norms.L2Operator Topology BigOperators ContDiff
variable {c f : Side} (r : Ratio c f) {b m w q δ s : ℝ}

lemma climb (L : Side) (b : ℝ) : armor L b 0=0 := by simp [armor,hedged]
@[fun_prop] lemma climb_c (L b) : Continuous (armor L b) := by unfold armor hedged; fun_prop

structure Radius (L : Side) (b m w q δ s : ℝ) : Prop where
  weak : Weak L b m w q
  pos : 0<δ
  between : q<s
  inside : s<1
  moats : q+w*armor L b δ ≤ s

lemma budgeted (L : Side) (h : Weak L b m w q) : ∃ δ s, Radius L b m w q δ s := by
  obtain ⟨s,ht,hx⟩ := exists_between h.aimed
  have he : Continuous fun d : ℝ => q+w*armor L b d := by fun_prop
  have hv : ∀ᶠ d : ℝ in 𝓝[>] 0, q+w*armor L b d<s := he.continuousAt.continuousWithinAt.eventually (gt_mem_nhds (by simpa only [climb,mul_zero,add_zero]))
  obtain ⟨d,hd,hq⟩ := (hv.and self_mem_nhdsWithin).exists; exact ⟨d,s,h,hq,ht,hx,hd.le⟩

section
variable (b m w : ℝ) (t : Site f) (n : ℕ)
def tiltL (P : Pulse f) := notch w (chute r t m b P)
lemma tether (U : Grid f) : tiltL r b m w t (settled U)=notch w (hefty r b t U m) := by simp only [tiltL,chute,hefty,estateQ,stated,pista]
@[fun_prop] lemma tilt_smooth : ContDiff ℂ ω (tiltL r b m w t) := contDiff_const.sub (ContDiff.const_smul (w:ℂ) (smoothH ..))

def alpha (P : Pulse f) := (w:ℂ) • tiltL r b m w t P ^ n
def bravo (P : Pulse f) := (b:ℂ)^2 • (loft r t P*alpha r b m w t n P*descent r t P)
def coin (x : Site f) (P : Pulse f) := -(∑ j : Fiber, plank (tiltL r b m w t P) (x,j) n)

@[fun_prop] lemma alpha_smooth : ContDiff ℂ ω (alpha r b m w t n) := ((tilt_smooth ..).pow _).const_smul (w:ℂ)
@[fun_prop] lemma bravo_smooth : ContDiff ℂ ω (bravo r b m w t n) := (matrixSmooth _ _ (matrixSmooth _ _ (smoothL ..) (alpha_smooth ..)) (smoothT ..)).const_smul ((b:ℂ)^2)
@[fun_prop] lemma coin_smooth (x : Site f) : ContDiff ℂ ω (coin r b m w t n x) := by
  unfold coin; refine ContDiff.neg ?_
  apply ContDiff.sum; intro i _
  let U : Sheet f →L[ℂ] ℂ := LinearMap.toContinuousLinearMap { toFun := fun M : Sheet f => M (x,i) (x,i), map_add' := fun _ _=> rfl, map_smul' := fun _ _=>rfl }
  exact (U.contDiff.comp ((tilt_smooth ..).pow (n+1))).div_const _
lemma a_still (U : Grid f) : alpha r b m w t n (settled U)=crumbs r b m w t n U := by simp only [alpha,tether]; rfl
lemma b_still (U : Grid f) : bravo r b m w t n (settled U)=barrel r b m w t n U := by simp only [bravo,a_still,stated,estateQ]; rfl
lemma c_still (x : Site f) (U : Grid f) : (coin r b m w t n x (settled U)).re=wither r b m w t n x U := by simp only [coin,tether,wither,Complex.re_sum,Complex.neg_re]
end

variable {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedSpace ℂ A] [NormedSpace ℂ B]
def toll (δ : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => toll δ n / (δ/2^(n+1))

lemma buys {X : A→B} (hX : ContDiff ℂ ω X) {d : ℝ} (hd : 0<δ) (x : A) (hb : ∀ y ∈ ball x δ, ‖X y‖ ≤ d)
    (k : ℕ) (y) (h : y ∈ ball x (δ /2^k)) : ‖iteratedFDeriv ℂ k X y‖ ≤ toll δ k * d := by
  induction k generalizing y with
  | zero => rw [norm_iteratedFDeriv_zero,toll,one_mul]; exact hb y (by simpa using h)
  | succ k ih =>
    have he : δ/2^(k+1)=(δ/2^k)/2 := by ring
    rw [← norm_fderiv_iteratedFDeriv,toll,he,div_mul_eq_mul_div]; rw [he] at h
    exact YM.Work.F02.fderiv_bound (hX.differentiable_iteratedFDeriv (by exact WithTop.coe_lt_top _)) (by positivity) ih h
section
variable (h : Radius r.count b m w q δ s) (t : Site f) (U : Grid f)
include h
lemma slopes (P : Pulse f) (hp : P∈ball (settled U) δ) : ‖tiltL r b m w t P‖ ≤ s := by
  have hb:=shields r t b m h.weak.active.le P U (δ:=δ) (by rw [mem_ball,dist_eq_norm] at hp; exact hp.le)
  have he:= norm_sub_norm_le (tiltL r b m w t P) (notch w (hefty r b t U m))
  have hh : ‖tiltL r b m w t P-notch w (hefty r b t U m)‖ ≤ w*armor r.count b δ := by
    unfold tiltL notch; rw [sub_sub_sub_cancel_left,norm_sub_rev, ← smul_sub,norm_smul, Complex.norm_real,Real.norm_of_nonneg h.weak.pos.le]
    exact mul_le_mul_of_nonneg_left hb h.weak.pos.le
  linarith only [he,hh,h.weak.draws t U,h.moats]
lemma grit (n) (P : Pulse f) (hp : P∈ball (settled U) δ) : ‖alpha r b m w t n P‖ ≤ w*s^n := by
  rw [alpha,norm_smul,Complex.norm_real, Real.norm_of_nonneg h.weak.pos.le]
  exact mul_le_mul_of_nonneg_left ((power_bill ..).trans (pow_le_pow_left₀ (norm_nonneg _) (slopes r h t U P hp) _)) h.weak.pos.le
lemma rocks (n) (P : Pulse f) (hp : P∈ball (settled U) δ) :
    ‖bravo r b m w t n P‖ ≤ b^2 * ((slope r.count+hedged r.count δ)*(w*s^n)*(slope r.count+hedged r.count δ)) := by
  rw [mem_ball,dist_eq_norm] at hp
  have hh := guards r t U P hp.le
  have ht:= votes_cost r t U
  rw [estateQ,stated] at hh
  let g:=slope r.count+hedged r.count δ
  have he : ‖loft r t P‖ ≤ g := by dsimp only [g]; linarith [(norm_sub_norm_le _ _).trans hh.1]
  have hy : ‖descent r t P‖ ≤ g := by
    dsimp only [g]; have hx:=(norm_sub_norm_le _ _).trans hh.2; rw [Matrix.l2_opNorm_conjTranspose] at hx; linarith
  have hg := (norm_nonneg _).trans he; have hs : 0≤s := h.weak.touch.trans h.between.le
  rw [bravo,norm_smul,norm_pow, Complex.norm_real, Real.norm_of_nonneg h.weak.active.le]
  refine mul_le_mul_of_nonneg_left ((Matrix.l2_opNorm_mul (loft r t P * _) _).trans (mul_le_mul ?_ hy (norm_nonneg _) (mul_nonneg hg (mul_nonneg h.weak.pos.le (pow_nonneg hs n))))) (sq_nonneg b)
  exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul he (grit r h t U n P (by rwa [mem_ball,dist_eq_norm])) (norm_nonneg _) hg)
lemma shells (n x) (P : Pulse f) (hp : P∈ball (settled U) δ) : ‖coin r b m w t n x P‖ ≤ Fintype.card Fiber * s^(n+1) := by
  rw [coin,norm_neg]; exact (norm_sum_le _ _).trans ((sum_le_sum (fun i _ => (plank_le _ (x,i) n).trans (pow_le_pow_left₀ (norm_nonneg _) (slopes r h t U P hp) _))).trans (le_of_eq (by simp)))

lemma word (n x k) : ‖iteratedFDeriv ℂ k (coin r b m w t n x) (settled U)‖ ≤ toll δ k*(Fintype.card Fiber * s^(n+1)) := buys (coin_smooth ..) h.pos _ (shells r h t U n x) _ _ (mem_ball_self (by have := h.pos; positivity))
end
end YM.QCD.Kit
