import YM.QCD.Raft.Loon

/-! # high alias transverse vanishes below mesh side. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Push.Loops Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace
variable {c f L:Side}{H V: Bed}{η A U:ℝ}{k:ℕ}{X Y:ℕ→Side}{T:Towers L}
variable (h: Signal X Y H V T η A U k)
lemma q_alive (l:Site L) (d:Axis): ContDiff ℝ ω (fun t=> q (gustP l t) d):= ((q_diff d).restrict_scalars ℝ).comp (going l)
include h
lemma unreal (a:Axis)(b:Aim)(l:Site L)(z:TypeFace 2) :
    let F(t:ℝ):=(profile (psi H V T (some a)) (strandT t) l *ᵥ (symbol 1 (strandT t) *ᵥ b)) z
    ContDiffAt ℝ ω F 0 ∧ F 0=0 ∧ HasDerivAt F 0 0:=by
  intro F
  let W t:=strandT t; let A:=fun t=> profile (psi H V T (some a)) (W t) l; let U t:=symbol 1 (W t)
  have he : W 0=0:=by simp [W,strandT]
  have hg: ContDiff ℝ ω W:= Complex.ofRealCLM.contDiff.smul contDiff_const
  have hX : ContDiffAt ℝ ω A 0:=(show ContDiffAt ℂ ω (fun p=> profile (psi H V T (some a)) p l) (W 0) from (by rw [he]; apply profile_diff (psi_strip h.more h.roof h.floorP h.extraZ h.deep (some a)) h.more; exact fun _=>by simp; linarith [h.more])).restrict_scalars ℝ|>.comp (f:=W) _ hg.contDiffAt
  have hV : ContDiffAt ℝ ω U 0:=(symbol_diff (r:=1)|>.restrict_scalars ℝ).comp (f:=W) _ hg.contDiffAt
  have hA : A 0=0:=by rw [show A 0=profile _ (W 0) l from rfl, he, blank_psi h]
  have hu:U 0=0:=by unfold U; simp [he,symbol,q,wedge]
  let M : Matrix (TypeFace 2) (TypeFace 1) ℂ→L[ℝ] ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun i=> (i *ᵥ b) z,map_add':=fun i j=>by rw [add_mulVec]; rfl,map_smul':=fun i j=>by rw [smul_mulVec]; rfl }
  have hx : ContDiffAt ℝ ω F 0:=by
    change ContDiffAt ℝ ω (fun t=> (A t *ᵥ (U t *ᵥ b)) z) _; unfold mulVec dotProduct; apply ContDiffAt.sum; intro i _; apply ContDiffAt.mul (Eyrie.smear hX z i); exact ContDiffAt.sum fun j _=> ContDiffAt.mul (Eyrie.smear hV _ j) contDiffAt_const -- matrix arity
  refine ⟨hx, (by change (A 0 *ᵥ _) _=_; rw [hA, zero_mulVec]; rfl),?_⟩
  change HasDerivAt (fun t=> ∑ i, A t z i * (U t *ᵥ b) i) _ _
  have hv : ∀ i:TypeFace 2, HasDerivAt (fun t=> A t z i *(U t *ᵥ b) i) 0 0:=by
    intro i; have hp : ContDiffAt ℝ ω (fun t=> (U t *ᵥ b) i) 0 := by unfold Matrix.mulVec dotProduct; exact ContDiffAt.sum fun j _=> ContDiffAt.mul (Eyrie.smear hV i j) contDiffAt_const
    convert! ((Eyrie.smear hX z i|>.differentiableAt (by simp)).hasDerivAt.mul ((hp.differentiableAt (by simp)).hasDerivAt)) using 1
    rw [hA,hu,zero_mulVec]; simp
  have ht := HasDerivAt.fun_sum (u:=univ) (fun i _=> hv i); rw [sum_const_zero] at ht; exact ht
lemma signal_test (i:ℕ)(v:Site L): Matches (gustP v (pulseG X i)) (aliasSite (Ratio.mk L (h.sizes i)) (step 0) v):=by rw [gustP,show strandT _ =_ from (causeT (X i)).symm]; exact alias_match (Ratio.mk L (h.sizes i)) (step 0) v
lemma marking (l:Site L)(hx:l≠0):∀ᶠ i in atTop,q (gustP l (pulseG X i)) (pole l)≠0:=by
  have he:= poles l hx
  refine ((Pearl.beam0.comp h.goes).eventually ((q_alive l (pole l)).continuous.continuousAt.eventually_ne ?_)); rw [gust_nil]; exact he
lemma vanished (l:Site L)(hx:l≠0)(b:Aim): Tendsto (fun i=> ((pulseG X i:ℂ))⁻¹ • stone T b l (pulseG X i)) atTop (𝓝 0):=by
  let a:=pole l; let p (t):= gustP l t; let P:= pulseG X; let R t:= q (p t) a; let g i:=R (P i)
  have hr: R 0≠0:=by unfold R p; rw [gust_nil]; exact poles l hx
  have ht: Tendsto g atTop (𝓝 (R 0)):=((q_alive l a).continuous.tendsto _).comp (Pearl.beam0.comp h.goes)
  apply tendsto_pi_nhds.mpr; intro j
  obtain ⟨d,rfl⟩:= axisEquiv.surjective j
  let Q (i):= (stone T b l (P i)) (coord d)/(P i:ℂ)
  have hh (k:TypeFace 2)(F:ℝ→ℂ)(g':ℂ)(hy:F=fun t=> g'*(profile (psi H V T (some a)) (strandT t) l *ᵥ (symbol 1 (strandT t) *ᵥ b)) k)(hp:∀ᶠ i in atTop,Q i=(F (P i) / (P i:ℂ))/g i^2): Tendsto Q atTop (𝓝 0):=by
    let G t:=(profile (psi H V T (some a)) (strandT t) l *ᵥ (symbol 1 (strandT t) *ᵥ b)) k
    have h:=unreal h a b l k; have hx: Tendsto (fun i=> F (P i)/(P i:ℂ)) atTop (𝓝 0):=by
      refine (apex ?_ ?_).comp (vanishes ‹_›); · rw [hy]; simpa only [mul_zero] using! (h.2.2).const_mul g'
      rw [hy]; change g'*G 0=_; rw [show G 0=_ from h.2.1,mul_zero]
    apply Tendsto.congr' (show (fun i=>F (P i)/(P i:ℂ)/g i^2)=ᶠ[atTop] Q from EventuallyEq.symm hp); have hP:=hx.div (ht.pow 2) (pow_ne_zero 2 hr); rw [zero_div] at hP; exact hP
  have hQ : Tendsto Q atTop (𝓝 0):=by
    rcases lt_trichotomy a d with hl|hl|hl
    · let z:PlaqAxes:=⟨(a,d),hl⟩
      refine hh (plaquette z) _ 1 rfl ?_
      filter_upwards [marking h l hx] with i hi; rw [← signal_amounts h i b l a]; let r:=p (P i); change Q i=(1*(q r a * ((symbol 1 r *ᵥ _) (plaquette z)))/_)/_
      rw [vapors_s (signal_test h i l)]; unfold Q stone cath shortG; rw [show axisEquiv.symm (coord d)=d from axisEquiv.symm_apply_apply _]; change q r a≠0 at hi; change (_-(_/q r a* q r d))/ _= (_* (q r a* (_-_))/ _)/ (q r a)^2; dsimp only [r,p,a,z,P]; unfold r p a P at hi; field_simp
    · subst d
      refine tendsto_const_nhds.congr' ?_; filter_upwards [marking h l hx] with i hi; unfold Q; change _ = stone _ _ l _ (coord (pole l)) /_; rw [chase T b l (P i) hi,zero_div]
    let z:PlaqAxes:= ⟨(d,a),hl⟩; refine hh (plaquette z) _ (-1) rfl ?_
    filter_upwards [marking h l hx] with i hi; rw [← signal_amounts h i b l a]; let r:=p (P i); change Q i=(-1*(q r a * ((symbol 1 r *ᵥ _) (plaquette z)))/_)/_
    rw [vapors_s (signal_test h i l)]; unfold Q stone cath shortG; rw [show axisEquiv.symm (coord d)=d from axisEquiv.symm_apply_apply _]; change q r a≠0 at hi; change (_-(_/q r a* q r d))/ _= (_* (q r a* (_-_))/ _)/ (q r a)^2; dsimp only [r,p,a,z,P]; unfold r p a P at hi; field_simp; ring
  change Tendsto (fun i=> (_:ℂ) * _) _ (𝓝 (0:ℂ)); refine hQ.congr' (Eventually.of_forall fun i=>by unfold Q; rw [div_eq_mul_inv,mul_comm]; rfl)
end YM.QCD.Raft
