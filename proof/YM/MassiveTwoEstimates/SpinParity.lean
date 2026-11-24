import YM.MassiveTwoEstimates.SpinPath
import YM.MassiveTwoEstimates.SpinPlane

/-! Every continuous lift of a full coordinate-plane rotation ends at the
negative spin unit of the concrete Euclidean group. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinParity
open Massive QCD.Lat Matrix
open scoped Matrix.Norms.Frobenius

theorem additive {w : Ortho.Skew} {p : ℝ → EuPin} (hp : EuPin.Path w p) (s t : ℝ) :
    p (s+t)=p s*p t := by
  have h := SpinPath.covering.eq_of_comp_eq (hp.2.1.comp (continuous_const.add continuous_id))
    (continuous_const.mul hp.2.1) (funext fun r => by
      change (p (s+r)).coord=(p s).coord*(p r).coord
      rw [hp.2.2,hp.2.2,hp.2.2,SpinPlane.addParameter]) (0:ℝ) (by simp [hp.1])
  exact congrFun h t

private theorem blades (a b : Axis) :
    ((-Complex.I) • (gamma a*g5))*((-Complex.I) • (gamma b*g5)) = gamma a*gamma b := by
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul_neg,Complex.I_mul_I,neg_one_smul]
  have hb : g5*gamma b = -(gamma b*g5) := by rw [five b,neg_neg]
  rw [←Matrix.mul_assoc (gamma a*g5),Matrix.mul_assoc (gamma a),hb,mul_neg,neg_mul,
    Matrix.mul_assoc (gamma a),Matrix.mul_assoc (gamma b),g5_sq,mul_one,neg_neg]

private theorem bladeSquare (a b : Axis) (h : a≠b) :
    (gamma a*gamma b)*(gamma a*gamma b) = -1 := by
  calc
    _ = gamma a*(gamma b*gamma a)*gamma b := by simp only [Matrix.mul_assoc]
    _ = -1 := by rw [clifford h.symm,mul_neg,neg_mul,←Matrix.mul_assoc (gamma a),
                        gamma_sq,one_mul,gamma_sq]

theorem full (a b : Axis) (h : a≠b) (p : ℝ → EuPin) (hp : EuPin.Path (Ortho.plane a b) p) :
    (p (2*Real.pi)).coord=1 ∧ (p (2*Real.pi)).matrix= -1 := by
  obtain ⟨ra,hra,ma⟩ := SpinAxes.reflection a
  obtain ⟨rb,hrb,mb⟩ := SpinAxes.reflection b
  change ra.coord=Signed.reflect a at hra
  change rb.coord=Signed.reflect b at hrb
  have same : (p Real.pi).coord=(ra*rb).coord := by
    change (p Real.pi).coord = ra.coord*rb.coord
    rw [hp.2.2,SpinPlane.half a b h,hra,hrb]
  have M : (ra*rb).matrix.val=gamma a*gamma b := by
    change ra.matrix.val*rb.matrix.val=_
    rw [ma,mb,blades]
  refine ⟨(hp.2.2 _).trans (SpinPlane.full a b h),?_⟩
  rw [two_mul,additive hp]
  apply Units.ext
  change (p Real.pi).matrix.val*(p Real.pi).matrix.val = -(1:Spike)
  rcases SpinFibres.euFiber (p Real.pi) (ra*rb) same with eq | op
  · rw [eq,M,bladeSquare a b h]
  · rw [op,Units.val_neg,neg_mul_neg,M,bladeSquare a b h]

end YM.MassiveTwoEstimates.SpinParity
#print axioms YM.MassiveTwoEstimates.SpinParity.additive
#print axioms YM.MassiveTwoEstimates.SpinParity.full
