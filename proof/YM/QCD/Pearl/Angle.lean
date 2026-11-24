import YM.QCD.Pearl.Steer

/-!
# tube and quadratic remainders at zero
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ E] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
variable {η C : ℝ}
lemma versa (f:E→F)(h:0<η)(s:E)(hf:∀ p∈ball s η,DifferentiableAt ℂ f p)(hp:∀ p∈ball s η,‖f p‖≤C)(x:E)(hx:x∈ball s (η/2/2)):
    ‖f x-f s-dew (x-s) f s‖ ≤ (C/(η/2)/(η/2/2))*‖x-s‖^2:=by
  letI: NormedSpace ℝ E:= NormedSpace.restrictScalars ℝ ℂ E
  let d:=η/2/2; let T:=C/(η/2)/d
  have hc:0≤C:= (norm_nonneg _).trans (hp s (mem_ball_self h)); have hd:0<d:=by unfold d; positivity
  have hb: ball s (η/2)⊆ball s η:= ball_subset_ball (half_le_self h.le)
  have he y (hy:y∈ball s η): AnalyticAt ℂ f y:= PolyDisc.finiteD _ ((show ∀ᶠ z in 𝓝 y,z∈ball s η from isOpen_ball.mem_nhds hy).mono fun j hj=> hf j hj)
  haveI := FiniteDimensional.complete ℂ F
  have ht : closedBall s (dist x s)⊆ball s d:= closedBall_subset_ball (mem_ball.mp hx)
  have hi y (hy:y∈closedBall s (dist x s)): ‖fderiv ℂ f y-fderiv ℂ f s‖≤ T*‖x-s‖:=by
    refine (Run.lastwig (fderiv ℂ f) (half_pos h) (fun i hv=> ?_) (fun i hi=> Run.wind h hf hp hi) (ht hy)).trans ?_
    · exact ((he i (hb hv)).contDiffAt (n:=ω)|>.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
    apply mul_le_mul_of_nonneg_left (by rwa [← dist_eq_norm, ← dist_eq_norm]) (by positivity)
  rw [pow_two,← mul_assoc]; apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun i hv=> (hf i (hb ((ball_subset_ball (show d≤η/2 by dsimp [d]; linarith)) (ht hv)))).hasFDerivAt.hasFDerivWithinAt) hi (convex_closedBall ..) (mem_closedBall_self (by positivity)) (mem_closedBall.mpr le_rfl)
lemma sided₂ (h:0<η)(f:ℂ→ℂ)(he:∀ p∈ball 0 η,DifferentiableAt ℂ f p)(hp:∀ p∈ball 0 η,‖f p‖≤C)(z : ℂ)(hz:‖z‖<η/4):
    ‖f z+f (-z)-2*f 0‖ ≤ 16*C/η^2 * ‖z‖^2:=by
  let c:= C/(η/2)/(η/2/2)
  have hc : 2*c=16*C/η^2:=by unfold c; ring
  have hu:=versa f h 0 he hp z (mem_ball_zero_iff.mpr (by rw [show η/2/2=η/4 by ring]; exact hz));
  have hv:=versa f h 0 he hp (-z) (mem_ball_zero_iff.mpr (by rw [show η/2/2=η/4 by ring,norm_neg]; exact hz)); rw [sub_zero] at hu; rw [sub_zero,norm_neg,dew,map_neg] at hv
  rw [show f z+f (-z)-2*f 0=f z-f 0-dew z f 0+(f (-z)-f 0-(-dew z f 0)) by ring]; exact (norm_add_le ..).trans ((add_le_add hu hv).trans_eq (by unfold c at hc; ring))

lemma bean (a b:Para):quad a-quad b=beam (a-b) (a+b):=by
  unfold quad beam; simp only [Prod.fst_sub,Prod.fst_add,Prod.snd_sub,Prod.snd_add,Pi.sub_apply,Pi.add_apply]
  have h (i:Axis): (a.2 i-b.2 i)*(a.2 i+b.2 i)=a.2 i^2-b.2 i^2:=by ring
  simp_rw [h,sum_sub_distrib]; ring
lemma bean_bill (a b:Para): ‖beam a b‖ ≤ 5*‖a‖*‖b‖:= by
  have he : ‖a.1*b.1‖≤ ‖a‖*‖b‖:= (norm_mul_le ..).trans (mul_le_mul (norm_fst_le a) (norm_fst_le b) (by positivity) (norm_nonneg _))
  refine (norm_add_le ..).trans ((add_le_add he ((norm_sum_le ..).trans (sum_le_sum fun i _=> show ‖a.2 i*b.2 i‖≤‖a‖*‖b‖ from ?_))).trans_eq ?_)
  · exact (norm_mul_le ..).trans (mul_le_mul ((norm_le_pi_norm a.2 i).trans (norm_snd_le a)) ((norm_le_pi_norm b.2 i).trans (norm_snd_le b)) (by positivity) (norm_nonneg _))
  simp [Axis]; ring
lemma vector_max (k : Momentum): ‖k‖^2≤lengthSq k:=by
  obtain ⟨i,h⟩ : ∃ i, ‖k‖=‖k i‖ := by
    rw [← coe_nnnorm]; change ∃ i, ↑(univ.sup fun i=>‖k i‖₊)=(‖k i‖:ℝ)
    obtain ⟨i,_,he⟩:=Finset.exists_mem_eq_sup univ univ_nonempty fun i=> ‖k i‖₊; exact ⟨i,by rw [he]; rfl⟩
  rw [h]; exact single_le_sum (fun i _=>sq_nonneg ‖k i‖) (mem_univ i)
lemma cap_base {p:Momentum}(h:p∈ baseCube): ‖p‖ ≤ Real.pi:= (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr (fun i => by nth_rw 1 [← cast_real h.1 i]; rw [Complex.norm_real]; exact h.2 i)
end YM.QCD.Pearl
