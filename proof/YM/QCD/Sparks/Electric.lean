import YM.QCD.Sparks.Tensor

/-! # extract a cover vertex family in native shares -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Cost Run Revolve Metric Push.Uniform
open Eyrie Quarry Tree RG Precision Rudder Flume Pine Finset Set
open YM.Further.PhysicalPeriodLimitF933 Macrame Jacobi
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n : Side} {S:SparkMesh} {C B r:ℝ} {k m:ℕ}

lemma float_norm : ∃ P:ℝ,0 ≤ P∧∀ A:Bundle, ∀ B:ℝ,0≤ B → (∀ i j, ‖A i j‖≤ B) → ‖A‖ ≤ P*B:=by
  let L : (Fiber→Fiber→ℂ) →L[ℂ] Bundle:= LinearMap.toContinuousLinearMap { toFun:=Matrix.of,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
  obtain ⟨K,h,H⟩:= prefers (X:=Fiber→Fiber→ℂ) (Y:=Bundle) L
  refine ⟨K,h,fun A B hp hb=> (show ‖A‖≤K*‖(fun i j=> A i j)‖ from H (fun i j=> A i j)).trans (mul_le_mul_of_nonneg_left ?_ h)⟩
  exact (pi_norm_le_iff_of_nonneg hp).mpr fun i=> (pi_norm_le_iff_of_nonneg hp).mpr (hb i)

lemma assistN (x : Site n)(h:0<r):Push.Uniform.Decay r 0 x≤ Real.exp (-(r/4)*Laurent.size (lift x)):=by
  apply Real.exp_monotone; have hv :(Laurent.size (lift x):ℝ)≤4*separation 0 x:=by exact_mod_cast city_length x
  nlinarith
lemma marks {F:trackG n}(hp:glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst F r C)(p:Plane n k)(hv:k≤2)(i j:Fiber):
    ‖dotP F k p i j‖ ≤ C*Decay r 0 p.1*∏ z, Decay r 0 (p.2 z).1:=by
  let x:Row n:=(0,i); let y:Row n:=(p.1,j); change ‖entry F 0 p.2 x y‖≤ _
  have H:=hp x y; have hF : ContDiffAt ℝ ω F 0:= matrix_g fun i h=> (hp i h).host
  clear hp
  interval_cases k
  · unfold entry; rw [iteratedFDeriv_zero_apply]; simp only [Finset.univ_eq_empty, Finset.prod_empty,mul_one]; exact H.born -- issue y p motive
  · unfold entry; rw [iteratedFDeriv_one_apply,Fin.prod_univ_one]; exact (by rw [show fderiv ℝ F 0 _ x y=_ from detailed hF ..]; exact H.walks (p.2 0))
  rw [Fin.prod_univ_two]; unfold entry
  rw [show (fun i : Fin 2=> Push.Uniform.bolt (p.2 i))=![Push.Uniform.bolt (p.2 0),Push.Uniform.bolt (p.2 1)] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩), ← iter _ _ hF, detail_sq hF]
  exact H.wandered (p.2 0) (p.2 1)
lemma pitch_sum (F:trackG n){P : ℝ}(hu:0 ≤ P)(hp:∀ A:Bundle,∀ B:ℝ,0≤ B → (∀ i j, ‖A i j‖≤ B) → ‖A‖ ≤ P*B) (p: Tilt k)
    (hr: 0<r)(hC:0 ≤ C)(h:glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst F r C)(hv:k ≤ 2):
    ‖design F p‖ ≤ P*C*aim (r/4) p := by
  unfold design; split
  next he =>
    let q:=down n p
    have hx x (v : Fin k):0 ≤ Decay r (n:=n) x (q.2 v).1:= (decay_pos ..).le
    have hm := hp (dotP F k q) (C*Decay r 0 q.1*∏ z,Decay r 0 (q.2 z).1) (mul_nonneg (mul_nonneg hC (decay_pos ..).le) (prod_nonneg (fun i _=>hx _ i))) (marks h q hv)
    change ‖(normedD F q)‖≤ _; unfold normedD; rw [norm_smul,pathLength,one_mul]; apply hm.trans; rw [mul_assoc P]; apply mul_le_mul_of_nonneg_left _ hu
    rw [mul_assoc C]; apply mul_le_mul_of_nonneg_left _ hC
    have hh : up n q=p:=he
    apply le_trans _ (le_of_eq (congr_arg (aim (r/4)) hh)) -- ambiguous
    rw [beam_bill]; exact mul_le_mul (assistN _ hr) (prod_le_prod (fun i _=>hx _ i) fun i _=> assistN _ hr) (prod_nonneg fun i _=> hx _ i) (Real.exp_pos _).le
  rw [norm_zero]; exact mul_nonneg (mul_nonneg hu hC) (aim_pos ..).le

structure Exhibit (S:SparkMesh)(F:S.Field)(k:ℕ)(r C:ℝ)(m:ℕ→ℕ)(P : Typewriter k):Prop where
 climbs: StrictMono m
 price i p: ‖design (F i) p‖≤ C*aim r (p:Tilt k)
 shape p : Tendsto (fun i=> design (F (m i)) p) atTop (𝓝 (P p))
 ceiling p: ‖P p‖≤ C*aim r p

lemma lantern (S:SparkMesh)(k:ℕ)(hv:k≤2)(r C:ℝ)(hr:0<r)(hC:0≤C) : ∃ a W, 0 < a∧0 ≤ W ∧ ∀ F:S.Field, (∀ i, glyph (traceG _) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (F i) r C)→∃ m P, Exhibit S F k a W m P := by
  obtain ⟨P,hp,H⟩:= float_norm
  let a:=r/4; let W:=P*C
  refine ⟨a,W,div_pos hr (by norm_num),mul_nonneg hp hC,fun F h=>?_⟩
  have H (i:ℕ) (p:Tilt k): ‖design (F i) p‖≤ W*aim a p:=pitch_sum _ hp H p hr hC (h i) hv
  let U (p:Tilt k):Set Bundle:= closedBall 0 (W*aim a p)
  have he : IsCompact ((Set.univ : Set (Tilt k)).pi U):= isCompact_univ_pi fun i => isCompact_closedBall ..
  have hz : ∀ i:ℕ,(design (F i))∈(Set.univ : Set (Tilt k)).pi U := fun i p _=>mem_closedBall_zero_iff.mpr (H i p)
  obtain ⟨K,hk,m,hm,h⟩:= he.isSeqCompact hz
  exact ⟨m,K,hm,H,(tendsto_pi_nhds.mp h),fun p=> mem_closedBall_zero_iff.mp (hk p (Set.mem_univ p))⟩
end YM.QCD.Sparks
