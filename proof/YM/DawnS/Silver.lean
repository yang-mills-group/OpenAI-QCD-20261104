import YM.DawnS.Trop
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexConjugate
local notation "K"=> timeAxis
local notation "P"=> RingS
local notation "I₀"=>Complex.I
variable (z:P)
lemma colS (x:P): spark ⟨-x.val, (by rw [mem_sphere_zero_iff_norm,norm_neg,flash])⟩= -spark x:=by
     ext1 a b; rw [sparkG,Matrix.neg_apply,sparkG, ← sum_neg_distrib]; refine Finset.sum_congr rfl fun t _=>?_ ; unfold thetaS; dsimp only; rw [inner_neg_right,Complex.ofReal_neg,neg_mul] -- ext1 matrix expects two ?
lemma starS : star (spark z)=spark z:=by unfold spark; rw [star_sum]; apply Finset.sum_congr rfl; intro i _; rw [star_smul,gamma_star]; simp
lemma antiS: spark z*gamma K= -(gamma K*spark z):=by
    unfold spark; rw [sum_mul,mul_sum,← sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; rw[Matrix.mul_smul,Matrix.smul_mul,clifford (Fin.castSucc_ne_last _),smul_neg]
lemma shine_self : spark z*spark z=1:=by
     let a(j:Fin 3):ℂ:= ↑(thetaS (base j) z); let g(i:Fin 3):= gamma i.castSucc; have hA : ∑ j:Fin 3,a j^2=1:=by unfold a; simp_rw [←Complex.ofReal_pow,ray,←Complex.ofReal_sum,← EuclideanSpace.real_norm_sq_eq,flash]; simp
     let C:=(2:Spike); let X(i j:Fin 3):= ((a i)*(a j)) • (g i*g j)
     have hx:spark z*spark z=∑ i:Fin 3,∑ j:Fin 3,X i j:=by unfold spark; rw[sum_mul]; simp_rw[Finset.mul_sum,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; rfl
     have he(i j:Fin 3):X i j+X j i=if i=j then a i ^2 • C else 0:=by
           unfold X g; rw [mul_comm (a j), ← smul_add]; by_cases h:i=j; · subst i; simp only[gamma_sq, if_true,pow_two]; congr 1; norm_num [C]
           rw [if_neg h,clifford (Fin.castSucc_injective _ |>.ne h),neg_add_cancel,smul_zero]
     have h:spark z*spark z+spark z*spark z=C:=by
           conv_lhs=> lhs; rw [hx];
           conv_lhs=> rhs; rw [hx,sum_comm];
           rw [← sum_add_distrib]; simp_rw [←sum_add_distrib, he]; simp only [sum_ite_eq,Finset.mem_univ,↓reduceIte]; rw [← Finset.sum_smul,hA,one_smul]
     ext a b; have hf:= congr_fun (congr_fun h a) b; rw [show C=1+(1:Spike) by norm_num[C],Matrix.add_apply,Matrix.add_apply] at hf; apply mul_left_cancel₀ (a:=(2:ℂ)) (by norm_num); simpa only [two_mul] using hf
noncomputable def lampS (v:Bool)(z:P):Spike:= if v then - (gamma K* shine (-1) z) else (shine 1 z*gamma K).transpose
lemma stamp (v: Bool): lampS v z= if v then 1+I₀ • (gamma K*spark z) else (1+I₀ • (gamma K * spark z)).transpose:=by
    cases v
    · simp only [lampS, Bool.false_eq_true,↓reduceIte, shine,Complex.ofReal_one,one_smul]; rw [sub_mul, gamma_sq, Matrix.smul_mul,antiS]; simp only[smul_neg,sub_neg_eq_add]
    simp only [lampS, ↓reduceIte,shine,Complex.ofReal_neg,Complex.ofReal_one]; rw [mul_sub, Matrix.mul_smul, neg_one_smul]; rw [gamma_sq, Matrix.mul_smul]; abel -- check first operand? 
noncomputable def sheen(z:P):Spike:=I₀ • (gamma K* spark z)
lemma sheet_s : star (sheen z)=sheen z:=by rw [sheen,star_smul,star_mul,gamma_star,starS,show star I₀= -I₀ from Complex.conj_I,antiS,smul_neg,neg_smul,neg_neg]
lemma pulseG: sheen z*sheen z=1:=by unfold sheen; rw [Matrix.smul_mul, Matrix.mul_smul,smul_smul, Complex.I_mul_I,←mul_assoc _ _ (spark z),mul_assoc _ (spark z) _,antiS]; simp only [mul_neg,neg_mul]; rw [←mul_assoc (gamma K),gamma_sq,one_mul, shine_self,neg_one_smul,neg_neg]
lemma powered(v:Bool): star (lampS v z) * lampS v z=((2:ℂ) • lampS v z):=by
    let S:=1+ sheen z; have he: star S=S:=by rw [show star S=star _+star _ from star_add ..,star_one, sheet_s];
    have hh:S*S=((2:ℂ) • S):=by have hg:=pulseG z; unfold S; rw [add_mul,mul_add,mul_add,one_mul,one_mul,mul_one,hg,two_smul]; abel
    cases v
    · change _=_; rw [stamp]; change star S.transpose*S.transpose= (2:ℂ) • S.transpose; rw [show star S.transpose=(star S).transpose from rfl, he,← Matrix.transpose_mul,hh,Matrix.transpose_smul]
    rw [stamp]; change star S*S=_; rw[he];exact hh
end YM.DawnS
