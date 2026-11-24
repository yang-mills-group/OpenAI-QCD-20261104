import YM.Work.G03
/-! # Finite sample series.Desired exact off-shell read through horizon. Mean and covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Set Tensor
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
-- P(shift), curvature accounting.Tab.Met
abbrev Parc := (Cover →₀ ℝ)
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{k m i j:ℕ}
noncomputable def sound (x:Cover→F): Parc →ₗ[ℝ] F:= Finsupp.linearCombination ℝ x
lemma fond (w:Parc)(x y:Cover→F): sound (x+y) w=sound x w+sound y w:=by simp [sound,Finsupp.linearCombination_apply,Finsupp.sum,smul_add, Finset.sum_add_distrib]
lemma vital (w:Parc)(x:Cover→F)(r:ℝ): sound (r • x) w=r • sound x w:=by unfold sound; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,Finset.smul_sum, Pi.smul_apply,smul_comm (w _) r]
lemma rune (x:Cover)(f:Cover→ F):sound f (Finsupp.single x 1)=f x:=by simp [sound]
noncomputable def strike (l:List Axis)(x:Cover):Parc:= match l with
  | []=> Finsupp.single x 1
  | a::v=> strike v (x+step a) - strike v x
lemma sip (l:List Axis)(f:Cover→F)(b x:Cover): sound (fun z:Cover=> f (z+b)) (strike l x)=sound f (strike l (x+b)):=by
    induction l generalizing x with
    | nil=>rw [strike,strike,rune,rune]
    | cons i l ih=>rw [strike,strike,map_sub,map_sub,ih,ih,add_right_comm x b]
lemma pond (a:Axis)(l:List Axis)(f:Cover→F)(x:Cover) : sound f (strike (a::l) x)=sound (fun z=>f (z+step a)-f z) (strike l x):=by
    rw [strike,map_sub,← sip]; simp_rw [show (fun z=> f (z+step a) - f z)=(fun z=> f (z+step a)) + (-1:ℝ) • f from funext fun i=> by simp [sub_eq_add_neg],fond,vital]; simp [sub_eq_add_neg] -- type
abbrev gross:= Work.G03.castPos
-- FUN.DOM orientation ℤ.N.A.
section FTC
variable [CompleteSpace F]
lemma sail (w:Parc)(f:Cover→ℝ→F)(h:∀ i,Continuous (f i)): sound (fun v=> ∫ r in (0:ℝ)..1,f v r) w=∫ r in (0:ℝ)..1,sound (fun i=>f i r) w:=by
    induction w using Finsupp.induction_linear with
    | zero=>simp
    | add u v hu hv=>
      simp_rw [map_add, hu,hv]; rw [intervalIntegral.integral_add] <;> refine Continuous.intervalIntegrable (?_) _ _ <;> unfold sound <;> simp_rw [Finsupp.linearCombination_apply,Finsupp.sum] <;> exact continuous_finsetSum _ fun i _=> continuous_const.smul (h i)
    | single a r=> simp [sound,intervalIntegral.integral_smul]
lemma by_rise (E: T E4 F (k+1))(h:Tensor.Sym E)(a:Axis)(x:Cover)(y:E4):
     diagonal E (gross (x+step a)+y)-diagonal E (gross x+y) = (k+1:ℕ) • ∫ r in (0:ℝ)..1, diagonal (E.curryLeft (basis a)) (gross x+(y+r • basis a)):=by
     let Z:=gross x+y; let J:= E.curryLeft (basis a); let g(r:ℝ):=Z+r • basis a; let c:ℝ:=(k+1:ℕ)
     have hd(r:ℝ) : HasDerivAt ((diagonal E) ∘ g) (c • diagonal J (Z+r • basis a)) r:=by
           have he:=Tensor.diag_smooth E 1; have hh: HasDerivAt g (basis a) r:=by simpa only [zero_add,one_smul] using! (hasDerivAt_const r Z).add ((hasDerivAt_id r).smul_const (basis a))
           exact (((he.differentiable one_ne_zero (g r)).hasFDerivAt.comp_hasDerivAt r hh)).congr_deriv (by rw [differential_diagonal E h]; exact (Nat.cast_smul_eq_nsmul ℝ ..).symm)
     have hg: Continuous g:=by unfold g; fun_prop
     have hc: IntervalIntegrable (fun r:ℝ=> c • diagonal J (g r)) volume (0:ℝ) 1:=Continuous.intervalIntegrable (Continuous.const_smul ((Tensor.diag_smooth J ∞).continuous.comp hg) _) _ _
     have he:= intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1) (fun u _ => hd u) hc
     rw [show gross (x+step a)=gross x+basis a from Work.G03.castPos_step x _,add_right_comm (gross x),← Nat.cast_smul_eq_nsmul ℝ]
     simp only [comp_apply,g,zero_smul,one_smul, add_zero, intervalIntegral.integral_smul,Z,add_assoc] at he; rw [add_assoc]; exact he.symm
-- coordinate convention.N
lemma plow (l:List Axis)(E:T E4 F l.length)(h:Tensor.Sym E)(x:Cover)(y:E4): sound (fun i=> diagonal E (gross i+y)) (strike l x)= Nat.factorial l.length • E (basis ∘ l.get):=by
    induction l generalizing x y with
    | nil=> rw [strike,rune, show Nat.factorial ([]:List Axis).length=1 from rfl, one_smul]; exact congr_arg E (Subsingleton.elim (α:=Fin 0 → E4) ..)
    | cons a t ih=>
      rw [pond]; let J:= E.curryLeft (basis a)
      have he(z:Cover) := by_rise E h a z y; rw [show (fun z:Cover=> diagonal E (gross (z+step a)+y)-diagonal E (gross z+y))= ((t.length+1:ℕ):ℝ) • (fun z:Cover=>∫ r in (0:ℝ)..1, diagonal J (gross z+(y+r • basis a))) from funext fun _=>(he _).trans (Nat.cast_smul_eq_nsmul ℝ ..).symm,vital]; rw [sail]; simp_rw [ih J (freeze_sym E h _)] -- rewrite?
      · rw [intervalIntegral.integral_const]; rw [sub_zero,one_smul,Nat.cast_smul_eq_nsmul, show (a::t).length.factorial=(t.length+1)*t.length.factorial from Nat.factorial_succ (t.length),← mul_smul]; apply congr_arg; unfold J; rw [ContinuousMultilinearMap.curryLeft_apply]; apply congr_arg; funext i; refine Fin.cases ?_ (fun k=>?_) i; all_goals simp
      intro i; exact (Tensor.diag_smooth J ∞).continuous.comp (by fun_prop)
lemma higher (l:List Axis)(h':j<l.length)(E:T E4 F j)(h:Tensor.Sym E)(x:Cover)(y:E4): sound (fun i=> diagonal E (gross i+y)) (strike l x)=0:=by
    induction l generalizing j x y with
    | nil=> simp at h'
    | cons a l ih=>
        rw [pond]
        cases j with
        | zero=> have H(z z':E4): diagonal E z=diagonal E z':=congr_arg E (Subsingleton.elim ..)
                 rw [show (fun z:Cover=>diagonal E (gross (z+step a)+y)-diagonal E (gross z+y))= 0 from funext fun i=> by dsimp only [Pi.zero_apply]; exact sub_eq_zero.mpr (H ..)]; simp [sound] -- simp
        | succ j=> let J:= E.curryLeft (basis a); have hJ:= freeze_sym E h (basis a); have hh(z:Cover):= by_rise E h a z y; rw [show (fun z:Cover=> diagonal E (gross (z+step a)+y)-diagonal E (gross z+y))=((j+1:ℕ):ℝ) • (fun z:Cover=>∫ r in (0:ℝ)..1,diagonal J (gross z+(y+r • basis a))) from funext fun _=>(hh _).trans (Nat.cast_smul_eq_nsmul ℝ ..).symm,vital,sail]; simp_rw [ih (show j<l.length by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using h') J hJ x]; simp
                   intro i; exact (Tensor.diag_smooth J ∞).continuous.comp (by fun_prop)
end FTC
end YM.Arise
#print axioms YM.Arise.plow
