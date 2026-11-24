import YM.QCD.Eyrie.Layout

/-! # combine sparsity and global circle bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat Kit Rudder
open Revolve Metric Quarry Push.Uniform Stationary YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {I X : Type} {k m : ℕ} {r a b c B R A S u:ℝ}
section
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
lemma slack {f:X→ℂ}{x:X}(h:ContDiffAt ℝ ω f x)(i:X)(he : ∀ y (t:ℝ), f (y+t • i)=f y) :
    blade i f x=0 ∧∀ v:X,Jacobi.mixed v i f x=0 ∧ Jacobi.mixed i v f x=0:=by
  have hh (x:X)(hx:ContDiffAt ℝ ω f x): blade i f x=0:=by
    have hu : HasDerivAt (fun p:ℝ=>x+p • i) i 0:=by convert (hasDerivAt_const (𝕜:=ℝ) 0 x).add ((hasDerivAt_id' (0:ℝ)).smul_const i) using 1 <;> first| rfl | simp
    have hD:=DifferentiableAt.hasFDerivAt (hx.differentiableAt (by simp))
    have hz : HasDerivAt (fun p:ℝ=> f (x+p • i)) (blade i f x) 0:= (show HasFDerivAt f _ (x+(0:ℝ) • i) by simpa using hD).comp_hasDerivAt 0 hu
    simp_rw [he] at hz; exact hz.unique (hasDerivAt_const (𝕜:=ℝ) _ _)
  refine ⟨hh x h,fun v=>?_⟩
  have hV : Jacobi.mixed v i f x=0:= (blade_same v ((h.eventually (by simp)).mono fun y ha=> show blade i f y=(fun _:X=>(0:ℂ)) y from hh y ha)).trans (blade_const v 0)
  refine ⟨hV,?_⟩; rw [iter _ _ h] at *; rw [iteratedFDeriv_two_apply] at *; rw [h.isSymmSndFDerivAt (by norm_num)]; exact hV -- sym lemma?
end
lemma axesCost (a:Road n): ‖axisCL _ (Push.Uniform.bolt a)‖ ≤1:= by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; change ‖((↑(Push.Uniform.bolt a i)):ℂ)‖ ≤ _; by_cases h:i=a <;> simp [Push.Uniform.bolt,h,Ne.symm]

variable {L : Sails n→ℂ}{f : Cnr n→ℂ}
lemma visas (hf: L ∘ axisCL (Road n)=f)(h: ContDiffAt ℂ ω L 0):ContDiffAt ℝ ω f 0:=by
  rw [← hf]; refine ContDiffAt.comp (f:=axisCL (Road n)) (x:=0) ?_ (axisCL (Road n)).contDiff.contDiffAt -- args
  rw [map_zero]; exact h.restrict_scalars ℝ
lemma liftRates (m:ℕ)(hf:L ∘ axisCL (Road n)=f)(h:ContDiffAt ℂ ω L 0)(v: Fin m→Cnr n) : iteratedFDeriv ℝ m f 0 v=iteratedFDeriv ℂ m L 0 (axisCL _ ∘ v):=by
  rw [← hf]; let Θ:= axisCL (Road n)
  rw [wired Θ (by rw [map_zero]; exact (h.restrict_scalars ℝ).analyticAt), map_zero]
  have he := (h.of_le (show (m:WithTop ℕ∞) ≤ ω from le_top)).restrictScalars_iteratedFDeriv (𝕜:=ℝ); rw [← he]; rfl
lemma itemizes (h : ContDiff ℂ ω L)(hf:L ∘ axisCL (Road n)=f)(hb:∀ i∈ball 0 R, ‖L i‖≤B)(hr:0<R)(v:Fin k→ Road n):
    ‖iteratedFDeriv ℝ k f 0 (Push.Uniform.bolt ∘ v)‖≤B*circleTax R k:=by
  rw [liftRates k hf h.contDiffAt]
  let U:=iteratedFDeriv ℂ k L 0
  apply (U.le_opNorm ..).trans (le_trans _ (outline _ hr h hb k 0 (mem_ball_self (by positivity))))
  apply mul_le_of_le_one_right (norm_nonneg _); simpa only [prod_const_one, Function.comp_apply] using Finset.prod_le_prod (s:=univ) (fun j _=> norm_nonneg (axisCL _ (Push.Uniform.bolt (v j)))) fun i _=> axesCost _

lemma spill (W : Bloom k)(hw : a*u + r ≤b) (ha : 0≤u)(j z : Site n)(hv:(separation j z:ℝ)≤ a * W.span) : W.paid r ≤ W.paid b*Decay u j z:= by
  unfold Bloom.paid Decay; rw [mul_right_comm (Real.exp _) W.price,← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ W.price_nn; apply Real.exp_monotone; nlinarith

def ticket (k : ℕ)(C R : ℝ) (W: Bloom k)(u:ℝ) := C*W.paid u*(1+circleTax R 1+circleTax R 2)
lemma record (W:Bloom k)(i j:Row n)(hr : 0<R) (ht:0<u)(he:r+5*u≤ b)(hz : 0≤c)
    (hf:L ∘ axisCL _=trailF W i j)(hp : ContDiff ℂ ω L)(hb : ∀ x∈ball 0 R, ‖L x‖≤c*W.paid r):
    Flock (traceG n) Push.Uniform.bolt (trailF W i j) i.1 u (ticket k c R W b *Decay u i.1 j.1) := by
  let F:=trailF W i j
  let S' (z:ℝ):= W.paid z
  have hn (z:ℝ):0≤S' z:=mul_nonneg (Real.exp_pos _).le W.price_nn
  have ht1:=circleTax_pos hr 1; have ht2:=circleTax_pos hr 2
  have hc : 0≤ ticket k c R W b:=by unfold ticket; apply mul_nonneg (mul_nonneg hz (hn b)); positivity
  let p:=Decay u i.1; have ht' z : 0< p z:=decay_pos ..
  have hx:=visas hf hp.contDiffAt
  by_cases H : stop i.1 W.tail=j.1
  swap
  · rw [show trailF W i j=(fun x=>0) from funext fun x=> by simp only [trailF,at_books,entryR,if_neg H]]; refine (Flock.hush _ ht).patron ?_; rw [norm_zero]; exact mul_nonneg hc (ht' _).le
  let L' := W.span
  have hm (y:Road n) : separation i.1 y.1 ≤2*L' ∨ (∀ v:Cnr n, Jacobi.mixed v (Push.Uniform.bolt y) F 0=0 ∧ Jacobi.mixed (Push.Uniform.bolt y) v F 0=0)∧ blade (Push.Uniform.bolt y) F 0=0:=by
    by_cases h:separation i.1 y.1≤2*L'; exact Or.inl h
    obtain ⟨e1,h2⟩:=slack hx (Push.Uniform.bolt y) (abort W i j y (lt_of_not_ge h)); exact Or.inr ⟨h2,e1⟩
  have hL : separation i.1 j.1 ≤ L':= H ▸ ((stopped W.tail i.1).trans (Nat.le_add_right _ _))
  have hJ : W.paid r≤ W.paid b *p j.1:=spill W (a:=1) (by linarith) ht.le _ _ (by rw [one_mul]; exact_mod_cast hL) -- tactic?
  let A:=c*(1+circleTax R 1+circleTax R 2); have hA:0≤A:=mul_nonneg hz (by positivity)
  have hh : ticket k c R W b= A*S' b:=by unfold A S' ticket; ring
  rw [hh]
  refine ⟨ht,by rw [← hh]; exact mul_nonneg hc (ht' _).le,hx,?_,fun z=>?_,fun z y=>?_⟩
  · rw [← hf]; simp only [Function.comp_apply,map_zero]
    refine (hb 0 (mem_ball_self hr)).trans ?_
    change c*W.paid r ≤ A*S' b*p j.1; rw [mul_assoc]; exact mul_le_mul (le_mul_of_one_le_right hz (by linarith)) hJ (hn _) hA
  · obtain hv|⟨-,h⟩:=hm z
    · have hg := itemizes hp hf hb hr ![z]; rw [iteratedFDeriv_one_apply] at hg
      apply hg.trans
      have he : W.paid (r+2*u)≤ W.paid b*p j.1:=spill W (a:=1) (by linarith) ht.le i.1 _ (by rw [one_mul]; exact_mod_cast hL)
      have hz' : W.paid r ≤ W.paid (r+2*u)*p (traceG n z):=spill W (a:=2) (by linarith) ht.le i.1 _ (by exact_mod_cast hv)
      have hv' := hz'.trans (mul_le_mul_of_nonneg_right he (ht' _).le); change _ ≤ A*S' b*p j.1*p (traceG n z); rw [mul_right_comm c,mul_assoc (A*S' b),mul_assoc A, ← mul_assoc (S' b)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : circleTax R 1≤1+circleTax R 1+circleTax R 2) hz) hv' (hn r) hA
    change ‖blade _ F _‖ ≤ A*S' b*p _*p _; rw [h,norm_zero]; exact mul_nonneg (mul_nonneg (hh ▸ hc) (ht' _).le) (ht' _).le
  rcases hm z with hv|⟨hh',-⟩
  · obtain hw|⟨h',-⟩:=hm y
    · have hg:=itemizes hp hf hb hr ![z,y]
      unfold F at * -- may remove
      rw [Jacobi.iter _ _ hx]; rw [show ![Push.Uniform.bolt z,Push.Uniform.bolt y]=Push.Uniform.bolt ∘ ![z,y] from funext fun i=> by fin_cases i <;> rfl]; apply hg.trans -- fix
      have he : W.paid (r+2*u+2*u)≤ W.paid b*p j.1:=spill W (a:=1) (by linarith) ht.le i.1 _ (by rw [one_mul]; exact_mod_cast hL)
      have hw' :=spill W (r:=r+2*u) (a:=2) (b:=r+2*u+2*u) (by linarith) ht.le i.1 (traceG n z) (by exact_mod_cast hv)
      have hp':=spill W (r:=r) (a:=2) (b:=r+2*u) (by linarith) ht.le i.1 (traceG n y) (by exact_mod_cast hw)
      have hk:= hp'.trans (mul_le_mul_of_nonneg_right (hw'.trans (mul_le_mul_of_nonneg_right he (ht' _).le)) (ht' _).le)
      have hhq:= mul_le_mul (show c*circleTax R 2 ≤ A from mul_le_mul_of_nonneg_left (by linarith : circleTax R 2 ≤ 1+circleTax R 1+circleTax R 2) hz) hk (hn _) hA
      change c*S' r*circleTax R 2 ≤ A*S' b*p j.1*(p _*p _); unfold p S'; linarith only [hhq] -- unfold in hhq?
    change ‖Jacobi.mixed _ _ F 0‖ ≤ A*S' b*p _*(p _*p _); rw [(h' _).1,norm_zero]; exact mul_nonneg (mul_nonneg (hh ▸ hc) (ht' _).le) (mul_nonneg (ht' _).le (ht' _).le)
  change ‖Jacobi.mixed _ _ F 0‖ ≤ A*S' b*p _*(p _*p _); rw [(hh' _).2,norm_zero]; exact mul_nonneg (mul_nonneg (hh ▸ hc) (ht' _).le) (mul_nonneg (ht' _).le (ht' _).le)
end YM.QCD.Eyrie
