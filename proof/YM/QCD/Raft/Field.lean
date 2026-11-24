import YM.QCD.Raft.Cap
import YM.Next.FREE_KERNELS.ZeroAlias
import YM.Next.FREE_KERNELS.PatchMean

/-! # pay via mean solve -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Push.Loops Matrix YM.Next.Free
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace
variable {c f n:Side}{L:Side}{η A G M:ℝ}{k:ℕ}
def feeG (P:Patch)(q:Momentum)(i:Axis):=∑ j:P.Points,(P.weight j:ℂ)*∑ k∈ Finset.range P.L.val, mode q (j.val+k • step i)
lemma collectedG (S:StepData c f)(p:Site f)(u:Momentum)(hp: Push.Loops.Matches u p)(b:Aim)(x:Axis):
    (cmat (Precision.mean S)*ᵥ vw p b) (0,coord x)=feeG S.patch u x*b (coord x):=by
  rw [cmat_apply, mean_run]
  unfold feeG; rw [Finset.sum_mul]; apply sum_congr rfl; intro j _; rw [mul_assoc ((↑(_ : ℝ)):ℂ),Finset.sum_mul]; congr 1; apply sum_congr rfl; intro i hi; unfold vw; dsimp only; rw [show axisEquiv.symm (coord x)=_ from axisEquiv.symm_apply_apply x, atPoint,show S.ratio.embed 0=0 from map_zero S.ratio.root,add_zero,hp.read,map_add,map_nsmul,wrap_step]
lemma treasured (P:Patch)(p:Momentum)(x:Axis): feeG P p x= P.L.val * (pullLine P x p) :=by
  have he k (w:Patch.Points P):mode p ((w:Cover)+k • (step x:Cover))=mode p w.val*twirl (p x) (k:ℕ) := by
    rw [mode_shift,← mode_scale, factor, Pi.smul_apply, nsmul_eq_mul]; unfold twirl; push_cast; congr 2; ring
  unfold feeG; simp_rw [he, ← mul_sum, ← mul_assoc _ (mode _ _), ← Finset.sum_mul,pays_roll]; unfold pullLine rail; field_simp [side_ne]
lemma tack (h:0<η)(H:Bed)(hp:H.metric.strip η G){p:Site n}{u:Momentum}(hh:Matches u p):
    Routed (Equiv.refl _) (Equiv.refl _) p p (cmat (Precision.K (H.metric.acts n))) ((symbol 1 (-u)).transpose * H.metric.read u * symbol 1 u):= by
  have hd (v:Momentum)(x:Site n)(h:Matches v x):Routed (Equiv.refl _) (Equiv.refl _) x x (cmat (d 1 n)) (symbol 1 v):= reading v 1 ▸ acts_routed _ (cobound_safe 1) h
  have he:Routed (Equiv.refl _) (Equiv.refl _) p p (cmat (d 1 n)).transpose (symbol 1 (-u)).transpose:= by
    simpa only [add_zero] using (Synced.routed_transpose (p:=0) (fun k=> ⟨_, by rw [add_zero]; exact hd _ _ (mon_matches k)⟩) (by simpa only [add_zero] using hd _ _ hh.neg))
  rw [Precision.K,cmat_mul,cmat_mul]; exact (he.mul (acts_routed _ (Row.rights _ _ hp h.le) hh)).mul (hd u p hh)

open scoped Matrix.Norms.L2Operator
def lanternP (H: Bed)(b:Aim)(t:ℝ):= let p:= strandT t; ((symbol 1 (-p)).transpose * H.metric.read p *symbol 1 p)*ᵥ b
lemma lampP (H:Bed)(hp:0<η)(he:H.metric.strip η G)(b:Aim): ContinuousAt (lanternP H b) 0:=by
  let P:=strandT; let A(x:Momentum):=(symbol 1 (-x)).transpose; let B(x:Momentum):=symbol 1 x; let M(x:Momentum):= (A x * H.metric.read x)* B x
  have hx : ContDiffAt ℂ ω M 0:= by
    refine analyticMul (analyticMul (analyticTranspose (symbol_diff.comp 0 (f:=fun p:Momentum=>-p) (by fun_prop))) (row_analytic he hp ?_)) symbol_diff
    intro i; simp; linarith
  have hm:P 0=0:=by unfold P strandT; simp
  let L: Matrix (TypeFace 1) (TypeFace 1) ℂ→ₗ[ℝ] Aim:= { toFun:=fun i=>i*ᵥ b,map_add':= fun _ _=>Matrix.add_mulVec ..,map_smul':=fun _ _=>Matrix.smul_mulVec .. }
  have hL:Continuous P:=Complex.ofRealCLM.continuous.smul continuous_const
  exact L.continuous_of_finiteDimensional.continuousAt.comp (f:=M ∘ P) ((show ContinuousAt M (P 0) by rw [hm]; exact hx.continuousAt).comp hL.continuousAt)
lemma lamp_nil (H:Bed)(b:Aim): lanternP H b 0=0:=by simp only [lanternP,strandT, Complex.ofReal_zero,zero_smul,show symbol 1 0=0 from by simp [symbol,wedge,q],Matrix.mul_zero,Matrix.zero_mulVec]
variable {j t:ℕ}{F:Flight j t}{X Y:ℕ→Side}{H V:Bed}{T:Towers F.L}{K: KernelChoices}
lemma invoiceG (h:Signal X Y H V T η A G k)(hx:V.metric.strip η M)
    (i:ℕ)(hi : Precision.Inputs (Orbit.Venue F K (h.sizes i)) (installed (Orbit.Venue F K (h.sizes i)).ratio T.A0) (H.metric.acts (Y i)) (V.metric.acts (X i))) (b:Aim)(a:Axis):
    let t':=pulseG X i
    ∑ l:Site F.L, feeG F.patch (gustP l t') a * shortG T b l t' (coord a)=b (coord a) - ((K.penalty)⁻¹:ℝ) * (lanternP V b t') (coord a):=by
  intro t'; let C:=X i; let n:=Y i; let S:= Orbit.Venue F K (h.sizes i); let Q:=S.ratio; let B:=installed Q T.A0
  let z:Cover:=step 0; let P:= vw (n:=C) (wrap C z) b
  have he := congr_arg (fun A:Matrix (Body 1 C) (Body 1 C) ℝ=> (cmat A*ᵥ P) (0,coord a)) hi.dual; dsimp only at he
  rw [cmat_mul, ← Matrix.mulVec_mulVec] at he; have hp := vw_raze Q z T.A0 (Row.rights _ _ ((h.deep.2.2.2 [] (Nat.zero_le _)).1) h.more.le) b
  change (cmat (Precision.mean S)*ᵥ (cmat B*ᵥ P)) _=_ at he
  rw [show cmat B *ᵥ P=_ from hp, sendS, Finset.sum_apply] at he
  have hM l := collectedG S (aliasSite Q z l) _ (signal_test h i l) (shortG T b l t') a
  have hx' : quant C z=strandT t':=causeT C
  rw [hx'] at he -- maybe
  apply Eq.trans _ (he.trans ?_)
  · apply Finset.sum_congr rfl; intro l _; exact (hM l).symm
  have ht:P (0,coord a)=b (coord a):=by unfold P vw; simp
  have hV : cmat (Precision.K (V.metric.acts C)) *ᵥ P=vw (wrap C z) (lanternP V b t'):=by
    unfold P; simp_rw [← vw_plane]; exact (tack h.more V hx (show Matches (strandT t') (wrap C z) from hx' ▸ quant_matches C z)).vector b
  have hh : cmat (1:Matrix (Body 1 C) (Body 1 C) ℝ)=1:=by ext i j; simp only [cmat_apply,approached,Matrix.map_apply,Matrix.one_apply]; split <;> simp
  change (cmat (1- (K.penalty⁻¹:ℝ) • (Precision.K (V.metric.acts C))) *ᵥ P) (0,coord a)=_
  rw [map_sub,hh,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply,map_smul,Matrix.smul_mulVec,hV,ht]
  simp only [Pi.smul_apply,vw,cell_origin,one_mul]; rfl
end YM.QCD.Raft
