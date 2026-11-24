import YM.QCD.Raft.Curl

/-! # receipts of the column at momenta sampled a different resolution each time

U = mean T, eta after histories. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Push.Loops Matrix
open scoped Topology BigOperators Matrix ContDiff Classical
variable {L c f n:Side}{T:Towers L}{H V:Bed}{η A U:ℝ}{k:ℕ}
abbrev Lens (i:Side) := Body 1 i → ℂ
abbrev Aim := TypeFace 1→ℂ
def pole (l: Site L):Axis:= if h:l=0 then 0 else (step_picks l h).choose
lemma poles (l:Site L) (hl:l≠0): q (mon l) (pole l)≠0:= sub_ne_zero.mpr (by rw [← (mon_matches l).step,pole,dif_neg hl]; exact (step_picks l hl).choose_spec)
def strandT (t:ℝ): Momentum:=(t:ℂ) • step 0
def gustP (l:Site L)(t:ℝ):= aliasAt (strandT t) l
@[simp] lemma gust_nil (l:Site L): gustP l 0=mon l:=by simp [gustP,aliasAt,strandT]
lemma going (l:Site L): ContDiff ℝ ω (gustP l):=by unfold gustP strandT; exact ((alias_diff l).restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.smul contDiff_const)
lemma causeT (n:Side):quant n (step 0)=strandT (Pearl.beamH n):=by ext1 i; simp only [quant,strandT,reciprocal,Pearl.beamH,Pi.smul_apply,smul_eq_mul, step_apply]; split_ifs <;> push_cast <;> ring

structure Signal (S :ℕ→Side)(M:ℕ→Side)(g:Bed)(h:Bed)(T:Towers L)(η G H:ℝ)(k:ℕ) :Prop where
 more : 0<η
 extraZ : 1 ≤ k
 deep : T.Deep η G k
 roof : g.dual_diag.strip η G
 floorP : h.diagonal.strip η H
 sizes i : (M i).val=(S i).val*L.val
 goes : Tendsto S atTop atTop
 diag i : g.diagonal.acts (M i)*g.dual_diag.acts (M i)=1
 valid (i:ℕ) : installed (Ratio.mk L (sizes i)) T.T*h.diagonal.acts (S i)*Exterior.d 1 (S i)=g.diagonal.acts (M i)*Exterior.d 1 (M i)*installed (Ratio.mk L (sizes i)) T.A0
 parity : Odd L.val
 harmony : Harmonic T
-- soft caustic: B_l(t) transverse representative removing fine gradient exactly
variable {X₀ Y:ℕ→Side}{T :Towers L}
abbrev pulseG (S:ℕ→Side)(j:ℕ):=Pearl.beamH (S j)
def shortG (T:Towers L)(b:Aim) (l:Site L)(t:ℝ)(i:TypeFace 1):=rayBudget (strandT t) b T l i

def cath (T:Towers L)(b:Aim)(l:Site L)(t:ℝ):= shortG T b l t (coord (pole l))/q (gustP l t) (pole l)
def stone (T:Towers L)(b:Aim)(l:Site L)(t:ℝ) (i:TypeFace 1):= shortG T b l t i-cath T b l t*q (gustP l t) (axisEquiv.symm i)
def bright (T:Towers L)(b:Aim)(t:ℝ)(i:TypeFace 1):= if i=coord 0 then 0 else shortG T b 0 t i
lemma chase (T:Towers L)(b:Aim)(l:Site L)(t:ℝ)(h : Exterior.q (gustP l t) (pole l)≠0): stone T b l t (coord (pole l))=0:=by
  unfold stone cath; rw [show axisEquiv.symm (coord (pole l))=pole l from axisEquiv.symm_apply_apply _,div_mul_cancel₀ _ h,sub_self]
open scoped Matrix.Norms.L2Operator
lemma short_curve (h:0<η)(ht:T.Deep η A k)(b:Aim)(l:Site L):ContDiffAt ℝ ω (shortG T b l) 0:=by
  let g(p:Momentum):=profile T.A0 p l
  have he: ContDiffAt ℝ ω g (strandT 0):= by simp_rw [strandT,Complex.ofReal_zero, zero_smul]; apply ContDiffAt.restrict_scalars (𝕜':=ℂ) ℝ; apply profile_diff ((ht.2.2.2 [] (Nat.zero_le _)).1) h; exact fun i=>by simp; linarith
  let X: Matrix (TypeFace 1) (TypeFace 1) ℂ→L[ℝ] Aim:=LinearMap.toContinuousLinearMap { toFun:=fun a=> a*ᵥ b,map_add':=fun _ _=>add_mulVec ..,map_smul':=fun _ _=>smul_mulVec .. }
  exact X.contDiff.contDiffAt.comp 0 (he.comp (f:=strandT) 0 (Complex.ofRealCLM.contDiff.smul contDiff_const|>.contDiffAt))
lemma vanishes (h : Signal X₀ Y H V T η A U k): Tendsto (pulseG X₀) atTop (𝓝[≠] 0):=tendsto_nhdsWithin_iff.mpr ⟨Pearl.beam0.comp h.goes, Eventually.of_forall fun i=> (Pearl.beamP _).ne'⟩
lemma apex {H:ℝ→ℂ} (h: HasDerivAt H 0 0)(hh:H 0=0): Tendsto (fun t:ℝ=> H t/ (t:ℂ)) (𝓝[≠] 0) (𝓝 0):=by
  apply (hasDerivAt_iff_tendsto_slope.mp h).congr'
  refine Eventually.of_forall (fun i=>?_); rw [slope_def_module,hh,sub_zero,sub_zero]; change ((↑(i⁻¹)):ℂ)*_= _; push_cast; ring
lemma blank_psi (h: Signal X₀ Y H V T η A U k)(a:Axis)(l:Site L): profile (psi H V T (some a)) 0 l=0:=by
  let P:=psi H V T (some a); have hp:=psi_cancels h.more h.roof h.floorP h.extraZ h.deep h.parity h.harmony a
  have he: Row.read P 0=0:=by
    ext i j; simp only [Row.read,Laurent.read,mode_constant,one_smul,Matrix.of_apply]; rw [← Complex.ofReal_tsum,show ∑' z,P i j z=0 from (hp i j).tsum_eq]; rfl
  unfold profile aliasMatrix; unfold P at he; rw [he,Matrix.mul_zero]; rfl
-- projected differentiated identity
lemma signal_amounts (h:Signal X₀ Y H V T η A U k)(i:ℕ)(b:Aim)(l:Site L)(r:Axis):
    let t:=pulseG X₀ i; let q':=gustP l t
    q q' r • (symbol 1 q' *ᵥ shortG T b l t)=profile (psi H V T (some r)) (strandT t) l *ᵥ (symbol 1 (strandT t) *ᵥ b):=by
  intro t q'
  have he:= relay_pitch h.more h.extraZ h.deep h.roof h.floorP (h.sizes i) (h.diag i) h.parity (h.valid i) (a:=r) (step 0) l b; dsimp only at he; rw [causeT (X₀ i)] at he; exact he
end YM.QCD.Raft
