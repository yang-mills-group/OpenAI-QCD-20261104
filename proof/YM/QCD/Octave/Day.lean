import YM.QCD.Octave.Seal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Pine
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free Reggae
open Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM
open scoped Matrix.Norms.L2Operator
variable {c f:Side}{S:StepData c f} (F:Forest S.ratio){β a b t u v Z w p r:ℝ}{N j l k i d:ℕ}
open Oasis
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {x y:E}{T:E→F}
lemma leo (h:0<a)(ht: ContDiffAt ℝ (↑i) T (a • x)): normJ i (fun y:E=>T (a • y)) x ≤ normJ i T (a • x)*a^i := by
   let L:= a • ContinuousLinearMap.id ℝ E; have he: ‖L‖≤ a:= ContinuousLinearMap.opNorm_le_bound _ h.le fun i=>by change ‖a • i‖≤_; rw [norm_smul,Real.norm_of_nonneg h.le]
   change ‖iteratedFDeriv ℝ i (T ∘ L) x‖≤ _; rw [Blaze.linear_pull L ht]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; simp only [prod_const, Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he _) (norm_nonneg _)
abbrev linkQ (T:E→F) := fun x=> T x-T 0-(fderiv ℝ T 0 x)
lemma day0 (hi: 2 ≤ i)(hc:ContDiffAt ℝ i T x): normJ i (linkQ T) x=normJ i T x:=by
     show ‖iteratedFDeriv ℝ i (T-(fun _=> T 0)- ⇑(fderiv ℝ T 0)) x‖ = normJ i T x
     unfold normJ; rw [iteratedFDeriv_sub_apply (show ContDiffAt ℝ i (T-fun _=>T 0) x from hc.sub contDiffAt_const) ((fderiv ℝ T 0).contDiff.contDiffAt), iteratedFDeriv_sub_apply hc contDiffAt_const]; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le hi
     have hz (t:E→L[ℝ] F): ‖iteratedFDeriv ℝ (i+1+1) t (x)‖=0:=by rw [← norm_iteratedFDeriv_fderiv,show fderiv ℝ (⇑t)=fun _=> t from funext fun _=> t.fderiv, iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] -- norm_zero
     rw [show 2+_=i+1+1 from by omega, norm_eq_zero.mp (hz _), iteratedFDeriv_succ_const, Pi.zero_apply,sub_zero,sub_zero]
lemma hour (hx:2≤j)(h:0<b)(hz:0≤u)(hv:∀ x: E, ‖x‖<b→ ContDiffAt ℝ j T x)(he: ∀ i:ℕ, 2≤ i → i≤j→∀ x,‖x‖<b → normJ i T x*b^i≤ u*b^2) (x:E)(hp: ‖x‖<1): Brush j (u*b^2) 1 (fun y=> linkQ T (b • y)) x:=by
   let V:= ball (0:E) 1; let f:= linkQ T; let W i:= f (b • i)
   have hm i (hi:i ∈ V): ContDiffAt ℝ j f (b • i) ∧ ‖b • i‖ < b:=by
      have ht : ‖b • i‖< b:=by rw [norm_smul,Real.norm_of_nonneg h.le]; exact mul_lt_of_lt_one_right h (mem_ball_zero_iff.mp hi)
      exact ⟨((hv _ ht).sub contDiffAt_const).sub (fderiv ℝ T 0).contDiff.contDiffAt,ht⟩
   have ha : (0:E)∈V:=mem_ball_self zero_lt_one; have HH:ContDiffAt ℝ j T 0:=hv _ (by simpa using h)
   have hu: fderiv ℝ f 0=0:=by
      let B:= fderiv ℝ T 0; have he:= ((HH.differentiableAt (by exact_mod_cast (show j≠0 from by omega))).hasFDerivAt.sub_const (T 0)).sub (B.hasFDerivAt (x:=0)); change fderiv ℝ f 0=0; exact he.fderiv.trans (sub_self _)
   have hw : ‖fderiv ℝ W 0‖=0:=by
      let L:= b • ContinuousLinearMap.id ℝ E; rw [show W=f ∘ L from rfl,fderiv_comp _ (show DifferentiableAt ℝ f (L 0) from (hm _ ha).1.differentiableAt (by exact_mod_cast (show j≠0 from by omega))) L.differentiableAt,map_zero,hu,ContinuousLinearMap.zero_comp,norm_zero]
   have hh:= Shellac.pools (f:=W) zero_lt_one le_rfl hx (mul_nonneg hz (sq_nonneg b)) (show (0:ℝ)≤0 from le_rfl) (fun i hi=>ContDiffAt.comp _ (hm i hi).1 (f:=fun i:E=> b • i) (by fun_prop)) ?_ ?_ x (mem_ball_zero_iff.mpr hp)
   rotate_left
   · intro i hi hI x hx'; have hy :=hm _ hx'; refine (leo (T:=f) (x:=x) (i:=i) h ((hy.1).of_le (by exact_mod_cast hI))).trans ((Eq.trans_le ?_ (he i hi hI _ hy.2))); exact congr_arg (fun t:ℝ=> t*b^i) (day0 hi ((hv _ hy.2).of_le (Nat.cast_le.mpr hI)))
   
   · intro i hi; interval_cases i
     · unfold normJ; simp [W,f,linkQ]
     rw [normJ,norm_iteratedFDeriv_one,hw,zero_mul]
   · simpa only [one_pow,mul_one,add_zero,mul_zero,inv_one] using hh
end YM.QCD.Octave
