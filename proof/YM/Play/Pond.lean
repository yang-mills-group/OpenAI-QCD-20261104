import YM.Play.Opal
import YM.Play.Bole
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera.Oce
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly ProbabilityTheory ConnectedActivityE6.Poll
open scoped BigOperators Topology ContDiff Classical Matrix InnerProductSpace
variable {ι A:Type}[Fintype ι][DecidableEq ι][Fintype A] (P: Matrix ι ι ℝ) (hP:P.PosSemidef)(M:Matrix A ι ℝ)(m:A→ℝ)
include hP
local notation "R"=> sweep P
-- Poll law.Bu
lemma pier (v:Body ι)(t : ℝ) : mgf (fun z=> inner ℝ v z) (sweep P) t = Real.exp (dotProduct v.ofLp (P *ᵥ v.ofLp) * t^2 / 2) := by
  let L := innerSL ℝ v
  let W := sweep P
  have X : IsGaussian W := by unfold W sweep; infer_instance
  have ht := IsGaussian.map_eq_gaussianReal (μ:=W) L
  rw [ContinuousLinearMap.integral_comp_id_comm] at ht
  have hV := covarianceBilin_multivariateGaussian (μ:=0) hP v v
  rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id] at hV
  change ProbabilityTheory.covariance L L W=_ at hV
  rw [covariance_self (show AEMeasurable L W from L.measurable.aemeasurable)] at hV
  change ProbabilityTheory.variance L W = dotProduct _ _ at hV
  have he : (∫ x, x ∂W)=0 := by unfold W sweep; simp
  rw [he,map_zero,hV] at ht; rw [show (fun z => inner ℝ v z) = L from rfl]
  change mgf _ W t=_
  rw [mgf_gaussianReal ht,Real.coe_toNNReal,zero_mul,zero_add]
  rw [← hV]; exact variance_nonneg _ _
  exact IsGaussian.integrable_id

def knock (U: Matrix A A ℝ)(h:U.IsSymm): Next.Rank.Normal.Symmetric A :=⟨fun i j=>(U i j:ℂ),fun i j=> by rw [show U i j= U j i from h.apply ..] ⟩
lemma quant : (M * P * M.transpose).IsSymm := by unfold Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_mul,transpose_transpose, show P.transpose=P from hP.isHermitian,Matrix.mul_assoc] -- real star defeq?
local notation "Q"=> knock (M*P*M.transpose) (quant P hP M)
noncomputable def surge (M:Matrix A ι ℝ)(m:A→ℝ)(v:Body ι):A→ℝ:= m+M*ᵥv.ofLp
lemma holler : Corolla R (surge M m) m Q:=by
   constructor; intro b; let v : Body ι:=WithLp.toLp 2 (vecMul b M); let k:=dotProduct v.ofLp (P*ᵥv.ofLp)
   have hv:k=∑ i,∑ j,b i*b j*(M*P*M.transpose) i j:=by
       unfold k; let q:ι→ℝ:=vecMul b M; change dotProduct (vecMul b M) (P*ᵥq)=_; rw [← dotProduct_mulVec, show q= M.transpose*ᵥ b from (mulVec_transpose ..).symm,mulVec_mulVec,mulVec_mulVec]; let L:= M * P * M.transpose; change dotProduct b (L*ᵥ b)= _; simp only [dotProduct, Matrix.mulVec,Finset.mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold L; ring
   have hz : (k:ℂ)=vie Q b:=by unfold vie; rw [hv]; push_cast; rfl
   have ht z: foo b (surge M m z)=foo b m+inner ℝ v z:=by
      change dotProduct b (m+M*ᵥ z.ofLp)=_; rw [dotProduct_add,dotProduct_mulVec]; apply congr_arg (foo b m+·)
      rw [PiLp.inner_apply]; simp only [RCLike.inner_apply, star_trivial]; exact dotProduct_comm .. -- inspect
   refine ⟨k,by rw [←hz,Complex.ofReal_re],hz,?_⟩; funext t; simp_rw [ht]; rw [mgf_const_add, pier P hP,← Real.exp_add]
end YM.QCD.Bera.Oce
#print axioms YM.QCD.Bera.Oce.holler
