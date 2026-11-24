import YM.Arise.Unit
import YM.Eden.Plank
/-! # Exact thermal orientation of all Wick mixed calibration probes at once -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free.Lyre
open Function Filter MeasureTheory Lattice Wilson QCD QCD.Lat TensorProduct Maxwell Maxwell.Free QCD.Grass Analysis YM.Arise.Range
open scoped Topology BigOperators ContDiff TensorProduct Matrix Matrix.Norms.L2Operator Classical -- reorder
variable {d e n m:ℕ}(a:Axis) (p q:E4)
local notation "Q" => Signed.reflect a
local notation "P" => Ortho.motion (Signed.reflect a)
noncomputable abbrev anti (a:Axis): E4→L[ℝ] E4:= -(Ortho.motion (Signed.reflect a)).toLinearIsometry.toContinuousLinearMap
local notation "R" => anti a
noncomputable def tone (a i:Axis) :ℝ:=if i=a then 1 else -1
lemma pitch (i: Axis): R (basis i) = tone a i • basis i:=by
    apply PiLp.ext; intro j; change (-(Ortho.move Q (basis i))) j=_; rw [PiLp.neg_apply,Signed.mirrored,PiLp.smul_apply,smul_eq_mul]; unfold tone; rw [YM.basis_eq]; split_ifs<;> simp_all
lemma hits (hq:q∈away):anti a q∈away:=by
    intro h; have ht:P q=0:= neg_eq_zero.mp h; exact hq ((P).injective (ht.trans (P).map_zero.symm))
lemma gauges (hq:q ≠ 0)(i: Axis) : Maxwell.grad i Maxwell.Green (R q)= tone a i * Maxwell.grad i Green q:=by
    have hp:=hits a q hq; have hx:‖R q‖=‖q‖:= (norm_neg _).trans (LinearIsometryEquiv.norm_map P q); rw [first_Green hp,first_Green hq,hx]; have he : R q i =tone a i *q i:=by change (-(Ortho.move Q q)) i=_; rw [PiLp.neg_apply,Signed.mirrored]; unfold tone; split_ifs<;>simp_all
    rw [he]; ring
local notation "Ha"=> gamma a
noncomputable def spinor (x:E4):Spike:= ∑ a:Axis, (- (Complex.ofReal (Maxwell.grad a Green x))) • gamma a
lemma spinor_at (s t: Pinor): spinor q s t= dirac s t q:=by
    unfold spinor dirac; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _=> by rw [neg_mul,mul_comm (gamma i s t)]; rfl
-- Spinor itself Hermitian, active inversion on ALL axes except one
lemma spinor_header (hq:q≠0) : Ha * spinor (R q) * Ha=star (spinor q):=by
   unfold spinor; rw [Matrix.mul_sum, Matrix.sum_mul]; simp_rw [star_sum]; refine Finset.sum_congr rfl fun i _=> ?_
   rw [gauges a q hq i, Complex.ofReal_mul, Matrix.mul_smul, Matrix.smul_mul, star_smul,gamma_star]; simp only [star_neg,Complex.star_def, Complex.conj_ofReal]; by_cases hu:i=a; · subst i; simp [tone]
   rw [tone, if_neg hu, Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,neg_neg, clifford (Ne.symm hu), neg_mul, Matrix.mul_assoc,gamma_sq,Matrix.mul_one,neg_smul,smul_neg]
noncomputable def toneL (a:Axis)(l:List Axis):ℝ:=(l.map (tone a)).prod
section L
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]
lemma composed (f:E4→F)(hs:∀ q∈away,ContDiffAt ℝ ∞ f q)(l:List Axis) (hq:q ≠ 0) : deriveL l (f ∘ R) q=toneL a l • deriveL l f (R q):=by
    induction l generalizing q with
    | nil=> change _=(1:ℝ) • _ ; rw [one_smul]; rfl
    | cons i l ih=>
       let G:=deriveL l f; have he:DifferentiableAt ℝ G (R q):= ((Arise.Range.balla l f away open_away hs) (R q) (hits a q hq)).differentiableAt (by simp); let x:=basis i
       have hx: DifferentiableAt ℝ (G ∘ R) q := he.comp q (R).differentiableAt; let v:=toneL a l
       have hm: deriveL l (f ∘ R) =ᶠ[𝓝 q] fun y=> v • G (R y):= Filter.Eventually.mono (show ∀ᶠ y in 𝓝 _,y∈away from open_away.mem_nhds hq) (fun y hy=> ih y hy)
       change Analysis.D x (deriveL l (f ∘ R)) q= toneL a (i::l) • Analysis.D x G _; rw[GermD x hm]; change fderiv ℝ (v • (G ∘⇑R)) q x= toneL _ _ • _
       rw [fderiv_const_smul hx,fderiv_comp q he _]; change v • (fderiv ℝ G (R q) ((fderiv ℝ _ q) x))=_
       rw [ContinuousLinearMap.fderiv, (show R x=_ from pitch a i),map_smul]; unfold toneL; rw [List.map_cons,List.prod_cons,mul_comm,mul_smul]; rfl
       exact (R).differentiableAt
lemma localAgree (l:List Axis)(f g:E4→F)(hp:∀ x∈away,f x=g x)(hq:q≠0) : deriveL l f q=deriveL l g q:=by induction l generalizing q with| nil=> exact hp _ hq | cons i l ih=> exact GermD _ (Filter.Eventually.mono (show ∀ᶠ y in 𝓝 _, y∈away from open_away.mem_nhds hq) (fun y hy=>ih y hy))
end L
-- Real-linear operations on Spike
noncomputable def pop : Spike→L[ℝ]Spike:=
    (((LinearMap.mulLeft ℂ Ha).comp (LinearMap.mulRight ℂ Ha)).restrictScalars ℝ).toContinuousLinearMap
lemma pop_at(x:Spike): pop a x=Ha*x*Ha:= (mul_assoc ..).symm
lemma glow : ∀ v∈away, ContDiffAt ℝ ∞ spinor v:=by
    intro v hv
    exact ContDiffAt.sum fun i _=> (((Complex.ofRealCLM.contDiff.contDiffAt.comp v (Maxwell.gradGradientSmooth hv i)).neg).smul (contDiffAt_const (c:=gamma i)) : ContDiffAt ℝ ∞ (fun v=> (-(Complex.ofReal (Maxwell.grad i Green v))) • gamma i) v)
-- directional word coherence
lemma pitchL (hq:q≠0)(l:List Axis):toneL a l • (Ha * deriveL l spinor (R q)*Ha)=star (deriveL l spinor q):=by
    let L :=(starL' ℝ : Spike≃L[ℝ] Spike).toContinuousLinearMap -- lookup
    have hq' : ∀ x∈away,ContDiffAt ℝ ∞ (spinor ∘ R) x:=by intro x hx; exact ContDiffAt.comp x (glow (R x) (hits a x hx)) (R).contDiff.contDiffAt
    have h: deriveL l (pop a ∘ (spinor ∘ R)) q= deriveL l (star ∘ spinor) q := localAgree q l _ _ (fun x hx=> (pop_at a _).trans (spinor_header a x hx)) hq
    rw [spiral open_away _ hq' l (pop a) q hq, composed a q spinor glow l hq,map_smul,pop_at] at h; exact h.trans (spiral open_away spinor glow l L q hq)
end YM.Massive.UV.Free.Lyre
#print axioms YM.Massive.UV.Free.Lyre.spinor_at
#print axioms YM.Massive.UV.Free.Lyre.pitchL
