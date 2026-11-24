import Mathlib.Analysis.Calculus.SmoothSeries
/-! Uniform per-grid costs can be summed on small-field neighborhoods.-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set
open scoped Topology BigOperators ContDiff
variable {I E F : Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F] {k N:ℕ}{f:I→E→F}{a:ℕ→I→ℝ}{U:Set E}
section
variable (ht:IsOpen U)(hv:IsPreconnected U)(hp:∀ i,ContDiffOn ℝ (N : ℕ∞ω) (f i) U)(hc:∀ i≤N,Summable (a i))(hg:∀ i≤N,∀ j x,x∈ U→ ‖iteratedFDeriv ℝ i (f j) x‖ ≤ a i j)
include ht hv hp hc hg
local notation "v₀" n=>iteratedFDeriv ℝ n (fun x=> ∑' i, f i x)
private lemma at_sum (x:E) (hx:x∈U)(hk:k<N) : HasFDerivAt (fun x:E=> ∑' i,iteratedFDeriv ℝ k (f i) x) (∑' i, fderiv ℝ (iteratedFDeriv ℝ k (f i)) x) x:= by
   let p i:= iteratedFDeriv ℝ k (f i); have he(i:I)(x:E)(hx:x∈U):DifferentiableAt ℝ (p i) x:= ((hp i x hx).contDiffAt (ht.mem_nhds hx)).differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hk)
   have hq: Summable fun i=>p i x:= .of_norm_bounded (hc _ hk.le) (fun i=> hg k hk.le i x hx)
   refine hasFDerivAt_tsum_of_isPreconnected (hc _ (Nat.succ_le_of_lt hk)) ht hv (fun i x hx=> (he i x hx).hasFDerivAt) ?_ hx hq hx
   intro i y hy
   rw [fderiv_iteratedFDeriv,comp_apply,LinearIsometryEquiv.norm_map]; exact hg _ hk i y hy
lemma iterated_sum (x:E)(hx:x∈U)(hk:k≤N): HasSum (fun i=>iteratedFDeriv ℝ k (f i) x) (iteratedFDeriv ℝ k (fun y=>∑' i,f i y) x):=by
    induction k generalizing x with
    | zero =>
      have h : Summable (fun i=>iteratedFDeriv ℝ 0 (f i) x):= .of_norm_bounded (hc _ hk) (fun i=>hg 0 hk i x hx)
      refine (show (∑' i, iteratedFDeriv ℝ 0 (f i) x)=iteratedFDeriv ℝ 0 (fun y=>∑' i,f i y) x from ?_) ▸ h.hasSum
      simp_rw [iteratedFDeriv_zero_eq_comp,comp_apply]; exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum.symm -- syntax map_tsum ne args implicit
    | succ k ih =>
      let v := (iteratedFDeriv ℝ k fun y=>∑' i,f i y)
      have he: v =ᶠ[𝓝 x] (fun p:E=>∑' i,iteratedFDeriv ℝ k (f i) p):=by filter_upwards [ht.mem_nhds hx] with y hy; exact (ih y hy (by omega)).tsum_eq.symm
      have h : Summable (fun i=>iteratedFDeriv ℝ (k+1) (f i) x):= .of_norm_bounded (hc _ hk) fun i=>hg _ hk i x hx
      have hp:= ((at_sum ht hv hp hc hg x hx hk).congr_of_eventuallyEq he).fderiv
      refine (show (∑' i, iteratedFDeriv ℝ (k+1) (f i) x)=iteratedFDeriv ℝ (k+1) (fun y=>∑' i,f i y) x from ?_) ▸ h.hasSum
      unfold v at hp; simp_rw [iteratedFDeriv_succ_eq_comp_left,comp_apply,hp]; exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) F).symm.toContinuousLinearEquiv.map_tsum.symm
lemma jobs : ContDiffOn ℝ (N:ℕ∞ω) (fun x=>∑' i,f i x) U := by
    let g(x:E):F:=∑' i,f i x; have hg'(k:ℕ)(hk:k≤N) : EqOn (iteratedFDerivWithin ℝ k g U) (fun x=>∑' i,iteratedFDeriv ℝ k (f i) x) U:=fun x hx=> ((iteratedFDerivWithin_of_isOpen k ht hx)).trans (iterated_sum ht hv hp hc hg x hx hk).tsum_eq.symm
    refine (contDiffOn_nat_iff_continuousOn_differentiableOn ht.uniqueDiffOn).2 ⟨?_,?_⟩
    · intro m hm; refine (continuousOn_tsum ?_ (hc m hm) (fun i y hy=>hg m hm i y hy)).congr (hg' m hm); intro i; refine ((hp i).continuousOn_iteratedFDerivWithin (Nat.cast_le.mpr hm) ht.uniqueDiffOn).congr (iteratedFDerivWithin_of_isOpen m ht).symm
    intro m hm; exact (show DifferentiableOn ℝ (fun x:E=>∑' i,iteratedFDeriv ℝ m (f i) x) U from fun x hx=> (at_sum ht hv hp hc hg x hx hm).differentiableAt.differentiableWithinAt).congr (hg' _ hm.le)
end
end YM.Massive.Patria
#print axioms YM.Massive.Patria.jobs
