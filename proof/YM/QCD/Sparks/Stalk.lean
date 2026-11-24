import YM.QCD.Sparks.Spring

/-! # Each path part reconstructs literally, not approximation on real neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Push.Uniform Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Work.F03 Revolve
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n:Side}{p k:ℕ}{r B:ℝ}{I:Type} {C:I→Bloom k}

def metastage (C:I→Bloom k)(n:Side): trackG n:=fun x=>dust C n (input su n x)
lemma serenity {C:I→Bloom k} (h:Fractal C r B)(he:0<r): ContDiffAt ℝ ω (metastage C n) 0:=by
  obtain ⟨w,E,hw,hp,H⟩:=attainable k he B; exact matrix_g fun i j=> (H I C h n i j).host

def epilogue (W: Bloom k)(x:Cnr n): Sheet n := Matrix.of (vowel W x)
lemma sector (W: Bloom k)(x:Cnr n):
    Tendsto (fun t:ℝ=> (t^k)⁻¹ • W.tonic 0 (input su n (t • x))) cutRay (𝓝 (epilogue W x)):=by
  exact tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> vok W x i j -- not defeq norm
lemma spring_flock (X : Cnr n):∃ C:ℝ, 0 ≤ C∧∀ᶠ t in cutRay,∀ W:Bloom k,
    ‖(t^k)⁻¹ • W.tonic 0 (input su n (t • X))‖ ≤ W.price*C:=by
  obtain ⟨c,h,hc⟩:= slots_bound (arm su n 1 X)
  refine ⟨c^k,pow_nonneg h _,?_⟩; filter_upwards [hc] with t hT W
  let U : Grid n:= input su n (t • X)
  let B i (j:Fin k):=t⁻¹ • (W.petals j).atSite U i
  have he i : (t^k)⁻¹ • W.taste U i= W.hues (B i):=by unfold Bloom.taste B; rw [tint_smul,inv_pow]
  have hb i j : ‖B i j‖≤c:=by unfold B U input; rw [map_smul]; exact hT ..
  have hv (i): ‖(t^k)⁻¹ • W.taste U i‖ ≤ W.price*c^k:=by
    rw [he]; unfold Bloom.hues; apply (norm_sum_le ..).trans; unfold Bloom.price; rw [sum_mul]; apply sum_le_sum; intro j _
    rw [norm_smul,mul_comm ‖W.coeff j‖]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [Complex.norm_real,Real.norm_eq_abs,Finset.abs_prod]; have hz q : |(B i q) (j q)| ≤ c:= (show _ ≤ ‖B i q‖ from by simpa only [EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul] using abs_real_inner_le_norm (EuclideanSpace.basisFun su.ColorIndex ℝ (j q)) (B i q)).trans (hb i q) -- equality
    simpa using Finset.prod_le_prod (s:=univ) (fun i' _=>abs_nonneg (B i i' (j i'))) (fun b _=> hz b)
  unfold Bloom.tonic; rw [← Matrix.smul_mul]; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (rotation_price (circle ..))).trans;
  erw [show ∀ (P:Sheet n), (t^k)⁻¹ • P= ((↑(t^k)⁻¹):ℂ) • P from fun _=> rfl, ride_smul]; exact rides_size _ (mul_nonneg W.price_nn (pow_nonneg h _)) _ _ hv
lemma sunrise (h:Fractal C r B)(x:Cnr n):
    Tendsto (fun t:ℝ=> (t^k)⁻¹ • metastage C n (t • x)) cutRay (𝓝 (∑' i,epilogue (C i) x)):=by
  unfold metastage dust; have he (t:ℝ): Summable fun i=>(C i).tonic 0 (input su n (t • x)):= (h.tonics ..).of_norm
  simp_rw [← tsum_const_smul'']
  obtain ⟨E,-,H⟩:= spring_flock (k:=k) x; exact tendsto_tsum_of_dominated_convergence (h.priced.mul_right E) (fun i=> sector (C i) x) (H.mono fun t ht i=> ht (C i))
lemma sunroof (X:Cnr n): ∃ C:ℝ,0 ≤ C ∧∀ W: Bloom k, ‖epilogue W X‖≤ W.price*C:=by
  obtain ⟨c,h,H⟩:=spring_flock (k:=k) X
  exact ⟨c,h, fun W=> le_of_tendsto (sector W X|>.norm) (H.mono fun i h=> h W)⟩
lemma bough (h:Fractal C r B)(x:Cnr n): Summable fun i=> ‖epilogue (C i) x‖:=by obtain ⟨W,-,H⟩:=sunroof (k:=k) x; exact (h.priced.mul_right W).of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> H _)
lemma sculpt (h:Fractal C r B)(hu:0<r)(n:Side):EmptyThrough (metastage C n) k ∧ ∀ x, surge (metastage C n) (fun _:Fin k=> x)=(k.factorial:ℝ) • ∑' i,epilogue (C i) x:=by
  have ht:= serenity (n:=n) h hu|>.analyticAt
  have HH:=ray_origin (f:=metastage C n) (s:=k) fun x=> ⟨_, sunrise h x⟩
  refine ⟨(rays_jet ht k).1 HH,fun x=>?_⟩
  have he:= tendsto_nhds_unique (ray_limit ht HH x) (sunrise h x); rw [← he]; unfold Tensor.coeff Tensor.diagonal; rw [_root_.smul_apply]; rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast k.factorial_ne_zero),one_smul]; rfl
end YM.QCD.Sparks
