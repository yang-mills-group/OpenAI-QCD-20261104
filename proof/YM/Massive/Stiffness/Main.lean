import YM.Pert.Kinetic.Tables
import YM.Extra.ITERATION_NO_LOSS.Transport
/-!
# Extend the pure perturbative kinetic estimator to the RG fermion-reference action

Uses larger collection of test directions, Hermitian-real convention on sign
waves. The actual noise phases are not being dropped in this calculation: it's applied
to an output in the **same** soft-block RG scheme with the action representation.
Test slope in the Hessian, path-dependent. Also price the added scalar action (from
fermion determinant ornament).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Stiffness
open Lattice RG Gauge Wilson Pert Pert.Kinetic Precision Function Filter Set
open Work.F03 AnalyticBridge.VerifiedReset Extra.Iteration -- avoid aperture
open scoped Topology BigOperators ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {E : PathData G} {p : Clip} {σ C Λ ν V r:ℝ} {Q:BudgetPoint}

-- deterministic scalar action on the flag-free region
noncomputable def classicalPath (p : Clip) (E : PathData G) (β : ℝ) (U : Config G n) := β * mainTerm p E U + Precision.loop E U
lemma line_smooth (v: Directions G n) (i:Edge (Site n)) : ContDiffAt ℝ ω (fun x=>G.mat (AnalyticBridge.VerifiedReset.line v x i)) 0:=by
   unfold AnalyticBridge.VerifiedReset.line increment; simp only [Pi.one_apply,mul_one, Pi.smul_apply]; exact G.exp_jet.contDiffAt.comp (f:=fun x:ℝ=> x • v i) 0 (by fun_prop)
lemma lineImpact (h:E.Bounds p σ C Λ) (v: Directions G n) (β : ℝ) :
    ContDiffAt ℝ 2 (classicalPath p E β ∘ AnalyticBridge.VerifiedReset.line v) 0 ∧
    iteratedDeriv 2 (classicalPath p E β ∘ AnalyticBridge.VerifiedReset.line v) 0 = 2*actualPath (p:=p) E β v:=by
    let f:= classicalPath p E β ∘ AnalyticBridge.VerifiedReset.line v; have hf : ContDiffAt ℝ ω f 0:= ((contDiffAt_const (c:=β)).mul (Work.F02.mainTerm_contDiffAt h (line_smooth v))).add (Extra.Iteration.action_smooth h.width h.two (line_smooth v)); have hh : ContDiffAt ℝ 2 f 0:= hf.of_le le_top
    have ht : Tendsto (fun t:ℝ=> f t / t^2) (𝓝[≠] 0) (𝓝 (actualPath (p:=p) E β v)):= multi_tangent h β v
    obtain ⟨h0,h1⟩:=value_slope_of_sq_limit hh.continuousAt ht; have h2:=tendsto_nhds_unique (taylor_limit_two hh h0 h1.deriv) ht
    refine ⟨hh,?_⟩; change iteratedDeriv 2 f 0= _; linarith
lemma all_rates (hR : E.Bounds p σ C Λ) (hn : 4≤n.val) (i j: Axis) (hij : i ≠ j) {c:G.Color} (hc : ‖c‖=1) (β:ℝ) :
    |(∑ b:Bool, actualPath (p:=p) E β (wave (n:=n) c b i j)) - β/2 * (Fintype.card (Site n))*(4*Real.sin (Full.mesh n/2)^2)| ≤ Fintype.card (Site n)*(Full.mesh n)^3 * windPrice σ C Λ β := by
    let K := (β / 2) * ↑(Fintype.card (Site n)) * (4 * Real.sin (Full.mesh n / 2)^2)
    let P(s:Signed):= ∑ b:Bool, ∑ x:Site n, costPath p E β (Bid.pulled (lift1 (wave c b i j)) s) x
    let w := (Fintype.card (Site n) : ℝ) *(Full.mesh n)^3*windPrice σ C Λ β
    suffices he : ∀ s : Signed,|P s-K| ≤ w by
      unfold actualPath Patch.average; rw [←Finset.mul_sum, Finset.sum_comm]
      let q := (Fintype.card Signed:ℝ); have hq : 0<q:= by dsimp only [q]; exact_mod_cast Fintype.card_pos (α:=Signed)
      change |q⁻¹ * (∑ s:Signed,P s) - K| ≤ w
      rw [show q⁻¹*(∑ s:Signed,P s)-K=q⁻¹*(∑ s:Signed,(P s-K)) by simp [Finset.sum_sub_distrib,q] at *; field_simp,abs_mul,abs_of_pos (inv_pos.mpr hq)]
      refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun s _=> he s)) (by positivity)).trans_eq ?_
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change q⁻¹*(q*w)=w; field_simp
    intro s
    obtain ⟨a,h,h'⟩ := waves_turn c i j s hn hij
    exact rate_branch hR hn (i:=s.perm.symm i) (j:=s.perm.symm j) (c:=a) (fun b=> (h b).trans hc) β (s.perm.symm.injective.ne hij) s (fun b=> wave c b i j) (fun b=>(converts_dir s hn ..).symm.trans (congrArg _ (h' b)))

def papyrus (E : PathData G) (W : ℕ→ Atom G 2) : PathData G:= { E with loop:=W }
lemma ornament_cost (E : PathData G) (W : ℕ→ Atom G 2) (h:E.Bounds p σ C Λ) (hw: Charged W r V) (hr:0<r) (hS:Silent W) (ht: SymmetricAtoms W):
    (papyrus E W).Bounds p (min r σ) C V:=by
   refine { width:=lt_min hr h.width, rows:=?_, metric:=h.metric,
            symTerms:=h.symTerms, two:=hw.mono (min_le_left ..) le_rfl,
            three:=Charged.mono h.three (min_le_right ..) le_rfl,
            four:=Charged.mono h.four (min_le_right ..) le_rfl,
            loopTerms:=fun i b=>⟨(hS i b).1.summable,fun l=> ((hS i b).2 l).summable⟩,
            loop_normal:=fun i b=>⟨(hS i b).1.tsum_eq,fun l=> ((hS i b).2 l).tsum_eq⟩,
            invariant:=fun i=> ⟨ht i,(h.invariant i).2⟩ }
   intro u; apply Push.AbsoluteSums.budget_mono (h.rows u)
   · intro j; positivity
   intro j; unfold papyrus; simp only; gcongr; exact min_le_right ..
lemma era (h:E.Bounds p σ C Λ) (W : ℕ→ Atom G 2) (hw: Charged W r V) (hr:0<r) (hS:Silent W) (ht: SymmetricAtoms W) (v: Directions G n):
    let f := Extra.Iteration.action W ∘ AnalyticBridge.VerifiedReset.line v
    ContDiffAt ℝ 2 f 0 ∧ iteratedDeriv 2 f 0=2*actualPath (p:=p) (papyrus E W) 0 v:=by
  intro f; apply Eq.mp (congr_arg (fun g:ℝ→ℝ=> ContDiffAt ℝ 2 g 0 ∧ iteratedDeriv 2 g 0=_) ?_) (lineImpact (ornament_cost E W h hw hr hS ht) v 0)
  funext x; unfold f comp classicalPath; simp only [zero_mul,zero_add]; rfl
end YM.Massive.Stiffness
#print axioms YM.Massive.Stiffness.era
#print axioms YM.Massive.Stiffness.all_rates
