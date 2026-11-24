import YM.QCD.Stew.Payday
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
/-! # Real projection on the Gauge pressure. No imaginary scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Reggae
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{p:BudgetPoint}{z u a r t:ℝ}{i j x:Site c}
open Port AnalyticBridge.VerifiedReset
variable {ι:Type}{E:Gem c N ι}
noncomputable def mud (X:EvenA c N):ℂ:=coef ∅ X.val
noncomputable def clay (c:Side)(N:ℕ):EvenA c N→L[ℂ]ℂ:=LinearMap.toContinuousLinearMap { toFun:=mud, map_add':=fun x y=>map_add (Grass.coef _) _ _,map_smul':= fun z x=> map_smul (Grass.coef _) z _ }
noncomputable def river (c:Side)(N:ℕ):EvenA c N→L[ℝ]ℝ:= -(Complex.reCLM.comp ((clay c N).restrictScalars ℝ))
noncomputable def baker (c:Side)(N:ℕ):ℝ→L[ℝ]EvenA c N:= (1:ℝ→L[ℝ]ℝ).smulRight 1
noncomputable def ocean (c:Side)(N:ℕ):ℝ→L[ℝ] EvenA c N:= - baker c N
lemma walks (x:EvenA c N)(p:Matrix (Modes c N) (Modes c N) ℂ):mud (sways p x)=mud x:=vacant p _
lemma mur (x:EvenA c N)(p:Matrix (Modes c N) (Modes c N) ℂ): river c N (sways p x)=river c N x:=by change -(mud _).re= -(mud _).re; rw [walks]
lemma yours (x:EvenA c N): mud (Regal c N x)=star (mud x):=(vacant _ (surf _ x.val)).trans (vax x.val)
lemma realP {x:EvenA c N}(hp:Regal c N x=x): mud x= -(river c N x:ℝ):=by -- coerces to ℂ inside neg?
    have hx := Eq.trans (congr_arg mud hp.symm) (yours x); change mud x= - ((-(mud x).re : ℝ) :ℂ); push_cast; rw [neg_neg]; refine Complex.ext rfl ?_; change _=0; have hh:=congr_arg Complex.im hx; simp only [Complex.star_def, Complex.conj_im] at hh; linarith
lemma gets (p:ℝ): baker c N p=p • (1:EvenA c N):=rfl
lemma gives (p:ℝ): mud (baker c N p)=(p:ℂ):=by
    change clay c N (baker c N p)=_
    rw [gets,show clay c N (p • (1:EvenA c N))=p • (clay c N 1) from map_smul ((clay c N).restrictScalars ℝ) ..]; change p • (coef ∅ (1:Dirac (Modes c N)))= _; rw [← mono_empty, Grass.read,Complex.real_smul]; exact mul_one _
lemma chooseP (x: EvenA c N)(hp: Regal c N x=x):mud (x-ocean c N (river c N x))=0:=by
    let p:=river c N x; change clay c N (x - _)= _; rw [map_sub]; unfold ocean; rw [ContinuousLinearMap.neg_apply,map_neg]; rw [show clay c N (baker c N p)=_ from gives p,show clay c N x= _ from realP hp,sub_self] -- p defeq
lemma through (u: OrbitG (Modes c N))(w:ℝ): u.passL (baker c N w)=baker c N w:=by rw [gets,eSM _ (phare u), map_one]
lemma thorough (u: OrbitG (Modes c N))(w:ℝ): u.passL (ocean c N w)=ocean c N w:=by unfold ocean; simp [through]
lemma sees (o:Site c)(x:EvenA c N)(h:0≤a): ‖river c N x‖≤ Sen o a x:=by
    change ‖-(coef ∅ x.val).re‖ ≤ visc (lens o) a x.val; rw [norm_neg]; apply (Complex.abs_re_le_norm _).trans; rw [pricesD _ h]; simpa [starch,pieD] using (single_le_sum (f:=fun s=> starch (lens o) a s * ‖coef s x.val‖) (a:= (∅:Finset (Keys c N))) (fun i _=> mul_nonneg (starch_pos _ h _) (norm_nonneg _)) (mem_univ _))
lemma vine (o:Site c)(u v:ℝ)(h:0≤v): Sen o v (baker c N u)=‖u‖:=by
    rw [gets, ← measures,show needle o N v (u • (1:EvenA c N))=u • needle o N v 1 from map_smul ((needle o N v).restrictScalars ℝ) .., norm_smul]; rw [measures]; change _*visc _ _ (1:Dirac (Modes c N))=_; rw [← mono_empty,sturdy _ ∅ h]; simp [starch,pieD]
lemma vintage (o:Site c)(u v:ℝ)(h:0≤v): Sen o v (ocean c N u)=‖u‖:=by rw [←measures,ocean,ContinuousLinearMap.neg_apply,map_neg,norm_neg,measures,vine _ _ _ h]
lemma spores (o:Site c)(X:Support c)(f:Grid c→EvenA c N)(hp:Woven o X p a f u)(h: shadeG f)(hr:0≤a):
    let g:= (river c N) ∘ f; p.Regular X g ∧ p.supBounds o X g u:=by
    intro g; have he V (hh: Healthy p.threshold X V):Chart p.order g V:= (river c N).contDiff.contDiffAt.comp 0 (hp.use V hh)
    refine ⟨⟨fun U V hv=>congr_arg (river c N) (hp.room U V hv),(river c N).continuous.measurable.comp hp.Borel,?_,he,fun V hh q l hy=>YM.Next.Foundations.left_has q hy (he V hh)⟩,hp.travel,?_⟩
    · intro k U; exact (mur (f (gauge k U)) (Lat.rotates N k)).symm.trans (congr_arg (river c N) (show sways (Lat.rotates N k) (f (gauge k U))=f U from Subtype.ext (h U k)))
    intro V hh l hl hv; unfold g; rw [Push.Local.left_linear (river c N) l (hp.use V hh) hl]; exact (sees o _ hr).trans (hp.pole _ hh l hl hv)
lemma gates (X:Support c)(w:ℝ): Gated X (baker c N w):=by rw [gets]; exact Territory.club _ _ _ (show Gated X (1:EvenA c N) from Subalgebra.one_mem _)
lemma gator (X:Support c)(w:ℝ): Gated X (ocean c N w):=by rw [ocean,ContinuousLinearMap.neg_apply,gets, ← neg_smul, ← gets]; exact gates ..
lemma wealthy (N:ℕ) (o: Site c)(X:Support c)(f:Grid c →ℝ)(h:p.Regular X f)(hp:p.supBounds o X f u)(ha:0≤a): Woven o X p a ((ocean c N) ∘ f) u:=by
    refine ⟨fun U V hv=>congr_arg (ocean c N) (h.sites _ _ hv),fun V=>gator X _,fun V hv=>(ocean c N).contDiff.contDiffAt.comp 0 (h.smooth V hv),?_,(ocean c N).continuous.measurable.comp h.borel,hp.1⟩
    intro V hv l hl he; rw [Push.Local.left_linear _ l (h.smooth V hv) hl,vintage _ _ _ ha]; exact hp.2 V hv l hl he
lemma reducible (b:Flavor N)(x:ℝ): feeF b (baker c N x)=0:=by
    rw [gets]; change meter b (x • (1:EvenA c N))=_; rw [show meter b (x • (1:EvenA c N))=x • (meter b 1:Sheet c) from map_smul ((meter (c:=c) b).restrictScalars ℝ) ..]; rw [show (meter b 1 : Sheet c)=0 from ?_,smul_zero]
    apply Matrix.ext; intro i j; change grasp (1:Dirac (Modes c N)) _ _=0; rw [←breast,show panel 2 (1:Dirac (Modes c N))=0 from ?_]
    · simp [grasp]
    rw [← mono_empty,past _ _ (homogeneous ∅),if_neg]; simp
lemma reduceF (b:Flavor N)(x:ℝ): feeF b (ocean c N x)= (0:Sheet c):=by unfold ocean; rw [ContinuousLinearMap.neg_apply]; exact (map_neg (meter b) _).trans (by change -feeF b (baker c N x)=_; rw [reducible,neg_zero])
end YM.QCD.Reggae
