import YM.MassiveTwoEstimates.BoostRotor

/-! The spin boost sends the Lorentzian time and longitudinal gamma
matrices into the actual hyperbolic rotation of that two-plane. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.BoostBasis
open Massive Mink Matrix QCD.Lat BoostRotor
open scoped BigOperators Matrix.Norms.Frobenius InnerProductSpace

def clockM : Spike := (-Complex.I) • clock

theorem hAxis (e : Ray) : generator e*axis e=clockM := by
  rw [generator,Matrix.smul_mul,Matrix.mul_assoc,reverse,mul_neg,←Matrix.mul_assoc,
    axisSquare,one_mul,smul_neg,clockM,neg_smul]

theorem axisH (e : Ray) : axis e*generator e= -clockM := by
  rw [generator,Matrix.mul_smul,←Matrix.mul_assoc,axisSquare,one_mul,clockM,neg_smul,neg_neg]

theorem hClock (e : Ray) : generator e*clockM=axis e := by
  simp only [generator,clockM,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc,
    clock,gamma_sq,mul_one,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]

theorem clockH (e : Ray) : clockM*generator e= -axis e := by
  rw [clockM,generator,Matrix.smul_mul,Matrix.mul_smul,←Matrix.mul_assoc,
    reverse,neg_mul,Matrix.mul_assoc,show clock*clock=(1:Spike) from gamma_sq _,mul_one,
    smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]

def conjugate (e : Ray) (r : ℝ) (X : Spike) := mat e r*X*mat e (-r)

theorem add (e : Ray) (r : ℝ) (X Y : Spike) :
    conjugate e r (X+Y)=conjugate e r X+conjugate e r Y := by
  simp only [conjugate,mul_add,add_mul]

theorem smul (e : Ray) (r : ℝ) (z : ℂ) (X : Spike) :
    conjugate e r (z • X)=z • conjugate e r X := by
  simp only [conjugate,Matrix.smul_mul,Matrix.mul_smul]

theorem mix (e : Ray) (r : ℝ) (X Y : Spike)
    (hx : generator e*X=Y) (xh : X*generator e= -Y)
    (yh : Y*generator e= -X) :
    conjugate e r X = (Real.cosh r:ℂ) • X+(Real.sinh r:ℂ) • Y := by
  let c : ℂ := Real.cosh (r/2)
  let s : ℂ := Real.sinh (r/2)
  have cc : (Real.cosh r:ℂ)=c*c+s*s := by
    have eq := Real.cosh_add (r/2) (r/2)
    rw [show r/2+r/2=r by ring] at eq
    dsimp only [c,s]
    exact_mod_cast eq
  have ss : (Real.sinh r:ℂ)=s*c+c*s := by
    have eq := Real.sinh_add (r/2) (r/2)
    rw [show r/2+r/2=r by ring] at eq
    dsimp only [c,s]
    exact_mod_cast eq
  have forward : mat e r*X=c • X+s • Y := by
    simp only [mat,binomial,add_mul,Matrix.smul_mul,one_mul,hx,c,s]
  have backward : mat e (-r)=c • (1:Spike)+(-s) • generator e := by
    simp only [mat,binomial,neg_div,Real.cosh_neg,Real.sinh_neg,Complex.ofReal_neg,c,s]
  rw [conjugate,forward,backward,cc,ss]
  simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_one,xh,yh,
    mul_neg,neg_smul,smul_neg,add_smul]
  module

theorem longitudinal (e : Ray) (r : ℝ) :
    conjugate e r (axis e)=(Real.cosh r:ℂ) • axis e+(Real.sinh r:ℂ) • clockM :=
  mix _ _ _ _ (hAxis e) (axisH e) (clockH e)

theorem temporal (e : Ray) (r : ℝ) :
    conjugate e r clockM=(Real.cosh r:ℂ) • clockM+(Real.sinh r:ℂ) • axis e :=
  mix _ _ _ _ (hClock e) (clockH e) (axisH e)

end YM.MassiveTwoEstimates.BoostBasis
#print axioms YM.MassiveTwoEstimates.BoostBasis.longitudinal
#print axioms YM.MassiveTwoEstimates.BoostBasis.temporal
