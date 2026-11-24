import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
/-! # Joint flag coefficient budgets
 Uses an analytic path in a fixed ball. Coefficients assessed simultaneously with absolute-sum prices. No cheap inverse in a finite volume: geometric aperture restart is used, not zero-free observables. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Analysis.Shelf
open Function Lattice Filter Topology Finset MeasureTheory Complex Set Metric
open scoped BigOperators Classical
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A][CompleteSpace A]
  [NormedAddCommGroup B][NormedSpace ℂ B][CompleteSpace B]{ι ξ:Type*}
-- unit complex coordinate
abbrev Roof (f:ℂ→A) := AnalyticOnNhd ℂ f (Metric.ball 0 1)
noncomputable def ampK {F: Type*}[NormedAddCommGroup F][NormedSpace ℂ F](f:ℂ→F)(n:ℕ):F:= ((n.factorial:ℂ)⁻¹) • iteratedDeriv n f 0
lemma Roof.expands {f:ℂ→A}(hp:Roof f)(z:ℂ)(he:‖z‖<1): HasSum (fun i=> z^i • ampK f i) (f z):=by
    refine (Complex.hasSum_taylorSeries_on_ball hp.differentiableOn (mem_ball_zero_iff.mpr he)).congr_fun (fun i=>?_); rw [sub_zero,ampK,smul_comm]
omit [CompleteSpace A] in
lemma amp_zero (f:ℂ→A): ampK f 0=f 0:=by simp [ampK]
local notation "Q"=>ball (0:ℂ) 1
omit [CompleteSpace A] in
lemma Roof.comes {f:ℂ→A}(hp:Roof f)(r:ℝ)(hr:0<r)(ht:r<1): DiffContOnCl ℂ f (ball 0 r):=by
   refine ⟨hp.differentiableOn.mono (ball_subset_ball ht.le),?_⟩; rw [closure_ball _ hr.ne']; exact hp.continuousOn.mono (closedBall_subset_ball ht)
lemma Roof.pays {f:ℂ→A}(hp:Roof f)(r x:ℝ)(n:ℕ)(hr:0<r)(ht:r<1)(h:∀ z∈ sphere (0:ℂ) r, ‖f z‖≤x): ‖ampK f n‖≤x/r^n:=by
   let s:ℝ:=n.factorial; unfold ampK; rw [norm_smul,norm_inv, Complex.norm_natCast]; have he :0<s:=(Nat.cast_pos.mpr (Nat.factorial_pos n))
   apply (mul_le_mul_of_nonneg_left (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr (hp.comes r hr ht) h) (inv_nonneg.mpr he.le)).trans_eq; change s⁻¹*(s*x/r^n) =_; rw [← mul_div_assoc]; rw [inv_mul_cancel_left₀ he.ne'] -- orientation
omit [CompleteSpace B] in
lemma projection (n:ℕ)(f:ℂ→A)(h:AnalyticAt ℂ f 0) (Y:A→L[ℂ] B) : ampK (Y ∘ f) n=Y (ampK f n):=by unfold ampK; simp only [iteratedDeriv_eq_iteratedFDeriv,ContinuousLinearMap.iteratedFDeriv_comp_left Y (h.contDiffAt (n:=↑n)) (Nat.cast_le.mpr (le_refl n)), map_smul]; rfl
lemma protectedBudget (f:ι→ℂ→A)(p:ι→ℝ)(s:Finset ι) (hp:∀ i∈s, Roof (f i))(he:0 ≤ p) (n:ℕ) (r:ℝ) (h:∀ z∈ sphere (0:ℂ) (1/2:ℝ), ∑ i∈s,p i*‖f i z‖≤ r) : ∑ i∈s,p i*‖ampK (f i) n‖ ≤ r*2^n:=by
    choose g hG hF using fun i=> exists_dual_vector'' ℂ (ampK (f i) n); let P(i:ι):= (p i:ℂ) • g i; let G(i:ι): ℂ→ℂ:=P i ∘ f i; let T:=∑ i∈s,G i
    have hR(i)(hi:i∈s):Roof (G i):=fun x hx=>((P i).analyticAt (f i x)).comp (hp i hi x hx) -- named?
    have hT: Roof T:= s.analyticOnNhd_sum (fun i hi=> hR i hi) -- wrong
    have hq: ∀ z ∈ sphere (0:ℂ) (1/2:ℝ), ‖T z‖≤r:=by
       intro z hz; unfold T; rw [Finset.sum_apply]; apply (norm_sum_le ..).trans; apply (Finset.sum_le_sum (g:=fun i=> p i*‖f i z‖) (fun i _=>?_)).trans (h z hz)
       change ‖(p i:ℂ) • g i (f i z)‖ ≤ _; rw [norm_smul,norm_real,Real.norm_of_nonneg (he i)]; apply mul_le_mul_of_nonneg_left _ (he i); exact ((g i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hG i))
    let x:= ∑ i∈s,p i * ‖ampK (f i) n‖; have hx : 0≤x := sum_nonneg (fun i _=>mul_nonneg (he i) (norm_nonneg _))
    have hm: ampK T n=(x:ℂ):=by
       have hA (i) (hi:i∈s): ampK (G i) n= (p i * ‖ampK (f i) n‖:ℝ):=by
           unfold G; rw [projection n (f i) (hp i hi 0 (by simp))]; push_cast; change (p i:ℂ) * g i _=_; rw [hF]; rfl
       unfold T; have hp : ampK (∑ i∈s,G i) n=∑ i∈s,ampK (G i) n:= by unfold ampK; rw [iteratedDeriv_sum (f:=G) (fun i hi=> (hR i hi 0 (by simp)).contDiffAt),Finset.smul_sum]
       rw [hp]; unfold x; rw [Complex.ofReal_sum]; exact sum_congr rfl hA
    have hp0:= Roof.pays hT (1/2) r n (by norm_num) (by norm_num) hq; rw [hm,norm_real,Real.norm_of_nonneg hx] at hp0; exact hp0.trans_eq (by rw [one_div,inv_pow,div_inv_eq_mul])
end YM.MassiveQCD.Analysis.Shelf
