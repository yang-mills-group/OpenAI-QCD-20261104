import YM.Massive.Pressure.Major
import YM.Massive.Finite.Strict

/-!
# Bare pressure estimates and penaltyZ
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Lattice RG Wilson Next.Rank SectorNext.Vacuum Finset Function MeasureTheory Filter QCD QCD.Lat
open scoped Topology BigOperators ENNReal Matrix.Norms.Frobenius
variable {n f : Side} {g β D : ℝ} {G : Gauge} (L : HaarBudget G)

lemma fee {u : G.El} (hu : G.chord u ≤ g) (hb : 0≤ β) (hk : β * g^2 ≤ D) : β * G.price u ≤ D/2:=by
  have h:= pow_le_pow_left₀ (G.chord_nonneg u) hu 2; rw [G.chord_price u] at h
  linarith only [mul_le_mul_of_nonneg_left h hb,hk]

lemma noiseZ (S : StepData n f) (hg : 0 < g) (he : g≤1) (hb : 0≤ β) (hk : β * g^2 ≤ 4) :
    L.small*g^G.lieDim * Real.exp (-(S.kernel.penalty * 2)) ≤ S.penaltyZ β G:=by
  let a := Real.exp (-(S.kernel.penalty*2)); let U := G.shell (g/4)
  let h : G.El → ℝ := fun _=>a; let μ := G.probHaar
  have hI : Integrable (U.indicator h) μ:= (integrable_const _).indicator (G.shell_meas _)
  have ht : ∀ u:G.El,U.indicator h u ≤ S.penaltyWeight β u:=by
    intro u; by_cases hu:u∈U
    · rw [Set.indicator_of_mem hu]; apply Real.exp_monotone; have he:= fee (((show G.chord u ≤ g/4 from hu)).trans (by linarith)) hb hk; linarith only [mul_le_mul_of_nonneg_left he S.kernel.penalty_pos.le]
    rw [Set.indicator_of_notMem hu]; exact (Real.exp_pos _).le
  have hp:=integral_mono hI ((S.penaltyWeight_cont β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ht; rw [integral_indicator (G.shell_meas _),show (∫ i in G.shell (g/4), h i ∂μ)= _ from ?_] at hp
  · exact (mul_le_mul_of_nonneg_right (L.low g hg he) (Real.exp_pos _).le).trans hp
  exact (show (∫ u in U,h u ∂μ)=μ.real U*a from setIntegral_const _)

lemma pure_wilson (hg : 0 < g) (he : g≤1) (hb : 0≤β) (hk : β * g^2 ≤ 2) (hn : 1<n.val) :
    Real.exp (-(Fintype.card (Site n):ℝ) * Fintype.card PlaqAxes) * (L.small*g^G.lieDim)^spare n ≤ Wilson.partition G n β:=by
  apply tree_ball (G:=G) hn (s:=g) (fun k U=> bare_gauge β U k) (fun i=>(bare_pos _ i).le) _ hg.le (mul_nonneg L.positive.le (by positivity)) (L.low _ hg he) (Real.exp_pos _).le
  · intro i hi; apply Real.exp_monotone
    unfold energy; rw [mul_sum]; apply le_trans _ (sum_le_sum (f:=fun _=>-(1:ℝ)) (fun u (_:u∈univ)=>?_))
    · simp only [sum_const,card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]; linarith only
    linarith only [fee (faceBound hi u) hb hk]
  refine ⟨(bare_cont _).measurable, 1,fun V=>(Real.norm_of_nonneg (bare_pos _ _).le).le.trans (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (energy_nonneg V)))⟩

open scoped ComplexOrder in
lemma wilson (L : HaarBudget su) {N : ℕ} (R : Regulator n N) (hg : 0 < g) (he : g≤1) (hm : ∀ i, -3 ≤ R.m i) (hb : 0≤ R.β)
    (hk : R.β*g^2≤2) (h2 : Even n.val) (hn : 4≤n.val):
    Real.exp (-(Fintype.card (Site n):ℝ)*Fintype.card PlaqAxes) * (L.small*g^su.lieDim)^spare n ≤ R.Z.re:=by
  let W := Wilson.partition su n R.β
  apply le_trans (pure_wilson L hg he hb hk (by omega)) _; have hH := (Complex.le_def.mp (Checker.lower R hb h2 hn)).1
  apply le_trans _ hH
  exact le_mul_of_one_le_right (Wilson.partition_pos _).le (Finset.one_le_prod (fun i _=>one_le_pow₀ (a:= 4+R.m i) (by linarith only [hm i])))

end YM.Massive.Pressure
#print axioms YM.Massive.Pressure.wilson
