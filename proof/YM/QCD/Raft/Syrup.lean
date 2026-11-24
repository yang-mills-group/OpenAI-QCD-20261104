import YM.QCD.Raft.Storm

/-! # periodic cost receipt for the Hessian for all high aliases -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Cost Push.Uniform Eyrie Stationary Quarry Run Kit YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {n: Side}{F:Cnr n→Sheet n}{r C D:ℝ}

def syrup (r C D:ℝ):ℝ:=(level 1 r C*pricesG r)^2*D+ level 2 r C*pricesG r*Real.sqrt D*Real.sqrt (Fintype.card Fiber)
lemma syrup_pos (h:0<r)(hr:0≤C)(hd:0≤D):0 ≤ syrup r C D:=by unfold syrup; have hh:=level_nn hr h 2; have hp:=pricepos h; positivity
lemma room (h:0<r)(hr:0≤C)(hd:0≤D)(ha: Eyrie.glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst F r C)(hk:IsUnit (F 0).det)(he:hs2 (F 0)⁻¹ ≤ D * cap n) (x:Cnr n):
    ‖Jacobi.mixed x x (presG F) 0‖ ≤ syrup r C D* ‖x‖^2 *cap n:=by
  have ht:= tollsP F (matrix_g fun i j=>(ha i j).host) hk; obtain ⟨hp,hx⟩:=periods h hr ha x
  rw [ht.2 x,Real.norm_eq_abs]; apply le_trans (Complex.abs_re_le_norm _) ((norm_sub_le ..).trans _)
  have hh:=cap_pos n
  apply le_trans (add_le_add ((htrace_two ..).trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hp 2) he (hsPos _) (sq_nonneg _))) ((htrace ..).trans (mul_le_mul_of_nonneg_right (mul_le_mul hx (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _) ((norm_nonneg _).trans hx)) (Real.sqrt_nonneg _))))
  apply le_of_eq; rw [Real.sqrt_mul hd,Fintype.card_prod,Nat.cast_mul]; -- inspect
  rw [show ((Fintype.card (Site n)):ℝ)=cap n from rfl, Real.sqrt_mul hh.le]; unfold syrup; generalize hz : Real.sqrt (cap n)=Q; rw [← show Q^2=cap n from hz ▸ Real.sq_sqrt hh.le]; ring
lemma size_brace (p:Site n)(b:Aim)(a:su.Color): ‖(brace (vw p b) a).1‖≤‖a‖*‖b‖ ∧‖(brace (vw p b) a).2‖ ≤ ‖a‖*‖b‖:=by
  have hp (i :Road n) : ‖a i.2.2‖≤‖a‖:= by
    calc
      _ = |inner ℝ (EuclideanSpace.basisFun su.ColorIndex ℝ i.2.2) a| := by simp only [EuclideanSpace.basisFun_inner,Real.norm_eq_abs]
      _ ≤ _ := (abs_real_inner_le_norm ..).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
  have hx (i): ‖vw p b i‖≤‖b‖:=by unfold vw; rw [norm_mul,show ‖cell p i.1‖=1 from ?_, one_mul]; exact norm_le_pi_norm b _; exact mode_real _ _ (real_frequency p) -- name
  constructor <;> apply (pi_norm_le_iff_of_nonneg (by positivity :0 ≤‖a‖*‖b‖)).mpr <;> intro i <;> unfold brace <;> dsimp only <;> rw [career_apply,norm_mul] <;> apply mul_le_mul (hp i) _ (norm_nonneg _) (norm_nonneg _)
  · exact (Complex.abs_re_le_norm _).trans (hx _)
  exact (Complex.abs_im_le_norm _).trans (hx _)
lemma ratedP (P:Cnr n→ℝ)(h:ContDiffAt ℝ ω P 0)(x:Lens n)(a:su.Color): scoreM P a x= Jacobi.mixed (brace x a).1 (brace x a).1 P 0+Jacobi.mixed (brace x a).2 (brace x a).2 P 0:=by unfold scoreM powerR pchain brace; simp_rw [pairR_eval _ _ _ _ h]
lemma rooms (h:0<r)(hr:0≤C)(hd:0≤D)(ha: Eyrie.glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst F r C)(hk:IsUnit (F 0).det)(he:hs2 (F 0)⁻¹ ≤ D * cap n) (a:su.Color):Trims (presG F) (2*syrup r C D * ‖a‖^2) a:=by
  intro p b; let x:= brace (vw p b) a; have he':=room h hr hd ha hk he; let K:=syrup r C D; have hh:0≤K:=syrup_pos h hr hd; have hP:0<cap n:=cap_pos _
  rw [ratedP _ (tollsP F (matrix_g fun i j=>(ha i j).host) hk).1]; apply (abs_add_le ..).trans
  apply (add_le_add (he' x.1) (he' x.2)).trans; apply le_trans ?_ (le_of_eq (show K*(‖a‖*‖b‖)^2*cap n+K*(‖a‖*‖b‖)^2*cap n=(2*K*‖a‖^2)*cap n*‖b‖^2 by ring)); change K* _*_+K*_ *_≤ _; gcongr; exacts [(size_brace ..).1,(size_brace ..).2]
end YM.QCD.Raft
