import YM.MassiveTwoEstimates.SpinAxes

/-! The charge-preserving hyperbolic spin matrices for an arbitrary real
boost direction in the target Wick convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.BoostRotor
open Massive Mink Matrix QCD.Lat SpinClifford
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius

def dir (e : Ray) := position e.val 0
def axis (e : Ray) := slash (dir e)
def clock : Spike := gamma timeAxis

theorem axisSquare (e : Ray) : axis e*axis e=1 := by
  have h : ‖dir e‖^2=1 := by simpa [dir,e.property] using Mink.squares (dir e)
  simpa [axis,h] using square (dir e)

private lemma clockSlash : slash (basis timeAxis)=clock := by
  classical
  simp [slash,basis_eq,ite_smul,clock]

theorem reverse (e : Ray) : clock*axis e=-(axis e*clock) := by
  have t := polarized (basis timeAxis) (dir e)
  have ort : inner ℝ (basis timeAxis) (dir e)=0 := by
    rw [basis_inner]
    exact time_position e.val 0
  rw [ort,clockSlash] at t
  apply eq_neg_of_add_eq_zero_left
  simpa [axis] using t

def generator (e : Ray) : Spike := Complex.I • (axis e*clock)

theorem generatorSquare (e : Ray) : generator e*generator e=1 := by
  have raw : (axis e*clock)*(axis e*clock)=-(1:Spike) := by
    calc
      _ = axis e*((clock*axis e)*clock) := by simp only [Matrix.mul_assoc]
      _ = -((axis e*axis e)*(clock*clock)) := by
        rw [reverse,neg_mul,mul_neg]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [axisSquare,clock,gamma_sq,one_mul]
  simp only [generator,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I,
    raw,neg_one_smul,neg_neg]

theorem generatorCharge (e : Ray) :
    generator e*chargeMatrix = -(chargeMatrix*(generator e).transpose) := by
  have two : (axis e*clock)*chargeMatrix=chargeMatrix*(clock*axis e).transpose := by
    rw [transpose_mul,Matrix.mul_assoc,show clock*chargeMatrix=-(chargeMatrix*clock.transpose) from chargeGamma _,
      mul_neg,←Matrix.mul_assoc,show axis e*chargeMatrix=-(chargeMatrix*(axis e).transpose) from chargeSlash _,
      neg_mul,neg_neg,Matrix.mul_assoc]
  rw [generator,Matrix.smul_mul,two,reverse,transpose_neg,mul_neg,smul_neg,
    transpose_smul,Matrix.mul_smul]

def binomial (e : Ray) (c s : ℂ) : Spike := c • (1:Spike)+s • generator e

theorem multiply (e : Ray) (a b c d : ℂ) :
    binomial e a b*binomial e c d=binomial e (a*c+b*d) (a*d+b*c) := by
  simp only [binomial,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    generatorSquare,mul_one,one_mul,add_smul]
  simp only [mul_comm c a,mul_comm d a,mul_comm d b,mul_comm c b]
  abel

def mat (e : Ray) (r : ℝ) : Spike := binomial e (Real.cosh (r/2):ℂ) (Real.sinh (r/2):ℂ)

theorem matInv (e : Ray) (r : ℝ) : mat e r*mat e (-r)=1 := by
  have hyp : (Real.cosh (r/2):ℂ)^2-(Real.sinh (r/2):ℂ)^2=1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq (r/2)
  rw [mat,mat,multiply,neg_div,Real.cosh_neg,Real.sinh_neg,Complex.ofReal_neg,
    show (Real.cosh (r/2):ℂ)*(Real.cosh (r/2):ℂ)+(Real.sinh (r/2):ℂ)* -(Real.sinh (r/2):ℂ)=1 from by linear_combination hyp,
    show (Real.cosh (r/2):ℂ)* -(Real.sinh (r/2):ℂ)+(Real.sinh (r/2):ℂ)*(Real.cosh (r/2):ℂ)=0 from by ring]
  simp [binomial]

def unit (e : Ray) (r : ℝ) : Spikeˣ :=
  ⟨mat e r,mat e (-r),matInv e r,by simpa using matInv e (-r)⟩

private theorem transCharge (e : Ray) (r : ℝ) :
    mat e r*chargeMatrix=chargeMatrix*(mat e (-r)).transpose := by
  simp only [mat,binomial,neg_div,Real.cosh_neg,Real.sinh_neg,Complex.ofReal_neg,
    add_mul,Matrix.smul_mul,one_mul,generatorCharge,smul_neg,transpose_add,
    transpose_smul,transpose_one,mul_add,Matrix.mul_smul,mul_one,neg_smul,transpose_neg,mul_neg]

theorem preserves (e : Ray) (r : ℝ) : KeepsC (unit e r) := by
  change mat e r*chargeMatrix*(mat e r).transpose=chargeMatrix
  rw [transCharge,Matrix.mul_assoc,←transpose_mul,matInv,transpose_one,mul_one]

theorem continuousMatrix (e : Ray) : Continuous (mat e) := by unfold mat binomial; fun_prop

end YM.MassiveTwoEstimates.BoostRotor
#print axioms YM.MassiveTwoEstimates.BoostRotor.generatorSquare
#print axioms YM.MassiveTwoEstimates.BoostRotor.preserves
#print axioms YM.MassiveTwoEstimates.BoostRotor.continuousMatrix
