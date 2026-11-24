import YM.TorusPCAC.Spin.Path

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Gamma and G5 sign covariance using exactly the project Spin convention -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Spin
open QCD QCD.Lat Lattice Finset NormedSpace Revolve
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius Kronecker
local instance : NormedAlgebra ℚ Spike := .restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _

lemma orientation (A : Ortho) : A.val.det * A.val.det = 1:=by
  nth_rw 1 [← Matrix.det_transpose]; exact (Matrix.det_mul _ _).symm.trans ( (congr_arg Matrix.det A.transp |>.trans Matrix.det_one)) -- orientation side
lemma made (Ω : Ortho.Skew) (t : ℝ): (Ortho.oneParameter Ω t).val.det=1:=by
  let u:= Ω.val; let A:= exp ((t/(2:ℝ)) • u); have he : exp (t • u)=A*A:=by
    unfold A; refine Eq.trans ?_ (exp_add_of_commute (Commute.refl _)); congr 1; rw [← add_smul]; ring_nf -- ring_nf smul inside
  unfold Ortho.oneParameter; dsimp only
  have hp: (A*A).det=1:=(Matrix.det_mul _ _).trans (orientation (Ortho.oneParameter Ω (t/2))); rw [show Ω.val=u from rfl]; exact (congrArg Matrix.det he).trans hp
lemma mirror_det (i : Axis): (Signed.reflect i).val.det= -1:=by
  let x (j : Axis) : ℝ:= if i=j then -1 else 1
  have hp: (Signed.reflect i).val= Matrix.diagonal x:=by ext j k; by_cases h₁:j=k
                                                         · rw [h₁]; simp [x,Signed.reflect,Signed.ortho,Signed.matrix_at,Signed.mirror]
                                                         simp [Signed.reflect, Signed.ortho, Signed.matrix_at,Signed.mirror,h₁,Ne.symm h₁];
  rw [hp,Matrix.det_diagonal]; simp [x]
lemma central_g5 (i j : Axis) : Commute (bivector i j) g5:=by
  change _*_= _*_
  unfold bivector; split; next=>simp
  rw [smul_mul_assoc,mul_smul_comm]; congr 1; rw [mul_assoc, five, ← mul_assoc g5, mul_neg, ← mul_assoc, five, neg_mul,neg_neg]
lemma mirror_anti (i:Axis): mirrorMatrix i * g5=-(g5*mirrorMatrix i):=by
  have he:= Lat.five i
  unfold mirrorMatrix; rw [smul_mul_assoc, mul_smul_comm, ← smul_neg, ← mul_assoc g5, show g5*gamma i= _ from clifford_g5,neg_mul,neg_neg]
    where clifford_g5 : g5*gamma i=-(gamma i*g5):=by rw [five,neg_neg]
lemma mirror_star (i:Axis):star (mirrorMatrix i)=mirrorMatrix i :=by
  unfold mirrorMatrix; rw [star_smul,star_mul,g5_star,gamma_star,star_neg,show star Complex.I= _ from Complex.conj_I,neg_neg, five]; simp
lemma sends_signed (s : Signed) (i) : direction s.ortho.val i= if s.flip i then -gamma (s.perm i) else gamma (s.perm i):=by
  unfold direction Signed.ortho; simp_rw [s.matrix_at]; split_ifs <;> simp [*, ite_smul]
lemma mirror_lifts (a : Axis) (i:Axis): mirrorMatrix a * gamma i=direction (Signed.reflect a).val i * mirrorMatrix a:=by
  have h:= (Swing.mir a).sends i; unfold Signed.reflect; rw [sends_signed]
  unfold mirrorMatrix; rw [five,smul_neg,neg_smul,neg_neg,smul_mul_assoc,mul_smul_comm,h] -- sign check

/-- Gamma represents real Pin. Chiral sign for use including all reflections. -/
structure Lift (A : Ortho × Rep): Prop where
  unitaryV : A.2.val ∈ unitary _
  sends (i) : A.2.val * gamma i=direction A.1.val i * A.2.val
  fifth : A.2.val * g5=(A.1.val.det • g5)*A.2.val

namespace Lift
lemma init : Lift 1:= by
  constructor
  · exact Submonoid.one_mem _
  · intro i; change 1*_=direction 1 i*1; simp
  change 1*g5= ((1:M4).det • g5)*1; simp
lemma mul {A B} (h : Lift A) (e : Lift B): Lift (A*B):=by
  constructor
  · exact Submonoid.mul_mem _ h.unitaryV e.unitaryV
  · intro i; change A.2.val*B.2.val*gamma i=direction (A.1.val*B.1.val) i*(A.2.val*B.2.val); rw [mul_assoc,e.sends,direction_mul,← mul_assoc]
    unfold direction; simp_rw [mul_sum,sum_mul,mul_smul_comm,smul_mul_assoc,h.sends];
    exact sum_congr rfl fun i _=> by rw [mul_assoc]; rfl
  change A.2.val*B.2.val*g5=((A.1.val*B.1.val).det • g5)*(A.2.val*B.2.val)
  rw [mul_assoc,e.fifth,← mul_assoc,Matrix.det_mul,mul_smul_comm,h.fifth]; simp only [smul_mul_assoc, mul_smul, smul_comm A.1.val.det B.1.val.det, mul_assoc]
lemma inv {A} (h : Lift A) : Lift A⁻¹ :=by
  let a:=A.2; let b:=A.1; let F:Spike:=a⁻¹.val
  have hu : a.val*F=1:=a.val_inv
  have ht : F*a.val=1:=a.inv_val
  constructor
  · have he : F=star a.val:=by rw [← one_mul (star _),← ht,mul_assoc,h.unitaryV.2,mul_one] -- test
    change F ∈ unitary _; rw [he]; exact Unitary.star_mem h.unitaryV
  · intro i
    change F*gamma i=direction b⁻¹.val i*F
    have hp : a.val*direction b⁻¹.val i=gamma i*a.val:=by
      calc
        _ = direction (b.val*b⁻¹.val) i*a.val:=by
          rw [direction_mul]; conv_lhs=> rhs; rw [direction]
          rw [mul_sum, sum_mul]; simp only [smul_mul_assoc,mul_smul_comm]; exact sum_congr rfl fun i _=> by rw [show a.val*gamma i=direction b.val i*a.val from h.sends i]
        _ = _ := by rw [show b.val*b⁻¹.val = 1 from b.property.2,direction_one]
    apply a.isUnit.mul_right_injective -- probably left
    change a.val*(F*gamma i)=a.val*(direction _ _ * F)
    rw [←mul_assoc,hu,one_mul,←mul_assoc a.val,hp,mul_assoc,hu,mul_one]
  change F*g5=(b⁻¹.val.det • g5)*F
  have he : b⁻¹.val.det*b.val.det=1:=(Matrix.det_mul _ _).symm.trans ((congr_arg Matrix.det b.property.1).trans Matrix.det_one)
  calc
    _ = F * (b⁻¹.val.det • (b.val.det • g5))*1 := by rw [smul_smul,he,one_smul,mul_one]
    _ = F * (b⁻¹.val.det • ((b.val.det • g5)*a.val))*F := by rw [← smul_mul_assoc, mul_assoc F _ F, mul_assoc _ a.val F,hu,mul_one,mul_one]
    _ = _ := by rw [show b.val.det • g5 * a.val=a.val*g5 from h.fifth.symm, mul_smul_comm, ← mul_assoc,ht,one_mul,smul_mul_assoc]
lemma certified (A : Pin) : Lift A.val :=by
  let a:= A.val
  suffices euclidean ≤ (show Subgroup _ from {carrier:= {x| Lift x},one_mem':=Lift.init,mul_mem':=fun h e=> Lift.mul h e,inv_mem':=fun h=> Lift.inv h}) from this A.property
  rw [euclidean, Subgroup.closure_le]; intro g hg; rcases hg with ⟨i,j,t,rfl⟩|⟨i,rfl⟩
  · change Lift (rotations i j t); constructor
    · simp only [rotations, evolves]; apply exp_mem_unitary_of_mem_skewAdjoint; change star _ = -(_ : Spike); rw [star_smul,bivector_skew,smul_neg,star_trivial]
    · exact fun k=> journey ..
    simp only [rotations,evolves,made,one_smul]; exact (((central_g5 i j).smul_left t).exp_left).eq -- exists?
  change Lift (mirrors i); constructor
  · exact ⟨(mirror_star i) ▸ mirrorMatrix_square i, (mirror_star i) ▸ mirrorMatrix_square i⟩
  · exact fun _=> mirror_lifts ..
  change mirrorMatrix i*g5= ((Signed.reflect i).val.det • g5)*_
  rw [mirror_det,mirror_anti,neg_smul,one_smul,neg_mul]; rfl
end Lift
end YM.TorusPCAC.Spin

#print axioms YM.TorusPCAC.Spin.Lift.certified
