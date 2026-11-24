import YM.QCD.Raft.Bilinear

/-! # projection work with a variable determinant. No similar formula for a logdet without gauge-invariant extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Lat Fog Stationary Eyrie Quarry Tavern Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace ComplexConjugate
variable {c f n:Side}{a:su.Color}{P: Cnr n→ℝ}
structure Loves (P:Cnr n→ℝ):Prop where
 peak: ContDiffAt ℝ ω P 0
 dew: ∀ x, blade x P 0=0
 vote (s:Signed): P ∘ orderTurn s=ᶠ[𝓝 0] P
 roam (x:Site n): P ∘ spaceShift x=ᶠ[𝓝 0] P
 gaze: force P
lemma flatten (h:Loves P)(v w: BaseSites su n)(x y:Cnr n): Jacobi.mixed (x-gradientA su n v) (y-gradientA su n w) P 0=Jacobi.mixed x y P 0:=by
  have he := adhesion P ![(v,x),(w,y)] h.gaze h.peak.analyticAt ?_
  · rw [iter _ _ h.peak, iter _ _ h.peak]; rw [show (fun i:Fin 2=> _) =![x-gradientA su n v,y-gradientA su n w] from ?_] at he -- infer
    exact he.trans (congr_arg (iteratedFDeriv ℝ _ _ _) (show (fun i:Fin 2=> (![ (v,x),(w,y)] i).2)=![x,y] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)))
    exact funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
  intro i hi hx; have he : i=1:=by omega
  subst i; ext1 p; simp only [iteratedFDeriv_one_apply]; exact h.dew _
lemma love_add (h:Loves P)(v w:Lens n)(x y:Body 0 n→ℂ)(a:su.Color):
    pchain (pairR a P) (v+Push.Loops.cmat (Exterior.d 0 n)*ᵥ x) (w+Push.Loops.cmat (Exterior.d 0 n)*ᵥ y)=pchain (pairR a P) v w:=by
  have he (v w:form 1 n)(x y:form 0 n) : pairR a P (v+(Exterior.d 0 n)*ᵥ x) (w+(Exterior.d 0 n)*ᵥ y)=pairR a P v w:=by
    rw [pairR_eval _ _ _ _ h.peak,pairR_eval _ _ _ _ h.peak]; rw [(career n 1 a).map_add,(career n 1 a).map_add,colored_G,colored_G]; have hf:=flatten h (-career n 0 a x) (-career n 0 a y) (career n 1 a v) (career n 1 a w); simpa only [map_neg,sub_neg_eq_add] using hf
  unfold pchain; simp_rw [joy_jump,vis_jump,see,believe,he]
lemma fix_line {L: Cnr n→L[ℝ] Cnr n} (h:Loves P)(he:P ∘ ⇑L =ᶠ[𝓝 0] P)(x y:Cnr n): Jacobi.mixed (L x) (L y) P 0=Jacobi.mixed x y P 0:=by
  have hv:= repeated x y he; rw [adapt L _ _ (by rw [map_zero]; exact h.peak),map_zero] at hv; exact hv
lemma wander (d x:Site n)(a:su.Color)(b:Aim):
    spaceShift x (career n 1 a (vision (vw d b)))=career n 1 a (vision ((cell d x) • vw d b)) ∧ spaceShift x (career n 1 a (desire (vw d b)))=career n 1 a (desire ((cell d x) • vw d b)):=by
  constructor <;> funext i <;> rw [towns] <;> simp only [career_apply, desire, vision,Pi.smul_apply,smul_eq_mul,vw,cell_add] <;> rw [mul_right_comm, mul_comm (cell d x), mul_assoc] -- inspect
variable (a) in
lemma pays_chain (h:Loves P)(x d e:Site n)(p q:Aim) : pchain (pairR a P) (vw d p) (vw e q)= (cell d x*star (cell e x))*pchain (pairR a P) (vw d p) (vw e q) :=by
  let J:=pairR a P; let T:=vw d p; let R:= vw e q
  suffices he:pchain J T R=pchain J (cell d x • T) (cell e x • R) by rw [pcV,pcD] at he; exact he.trans (by unfold J; rw [← mul_assoc,mul_comm (star _)])
  unfold J pchain; simp only [pairR_eval _ _ _ _ h.peak]; have ht (u v : Cnr n):= fix_line h (h.roam x) u v
  have hd:=wander d x a p; have he:=wander e x a q
  dsimp only [T,R]; simp_rw [← hd.1,← hd.2,← he.1,← he.2,ht]
lemma page_chain (h:Loves P)(d e:Site n)(p q:Aim)(he:d≠e):pchain (pairR a P) (vw d p) (vw e q)=0:=by
  obtain ⟨i,hi⟩:= step_picks (d-e) (sub_ne_zero.mpr he); let x:Site n:= step i
  have hp:=pays_chain a h x d e p q; rw [show cell d x*star (cell e x)=cell (d-e) x from ?_] at hp; by_contra hy
  · apply hi; exact mul_right_cancel₀ hy (hp.symm.trans (one_mul _).symm)
  rw [sub_eq_add_neg,cell_duality (d+_),cell_add,cell_inverse,cell_duality x d]; congr 1; rw [Complex.star_def, cell_bar,cell_duality e x]
end YM.QCD.Raft
