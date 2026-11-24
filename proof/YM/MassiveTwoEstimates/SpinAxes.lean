import YM.MassiveTwoEstimates.SpinReflection

/-! Canonical signed axis lifts and the same spin matrix on the Euclidean
and Lorentzian spatial subgroups of the massive target. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinAxes
open Massive QCD.Lat Mink Matrix SpinReflection
open scoped BigOperators InnerProductSpace

private theorem onBasis (a : Axis) : slash (basis a) = gamma a := by
  classical
  simp [slash,basis_eq,ite_smul]

theorem reflection (a : Axis) :
    ∃ p : EuPin, p.Lifts (Signed.mirror a) ∧ p.matrix.val=(-Complex.I) • (gamma a*g5) := by
  obtain ⟨p,hp,act⟩ := unitMirror (basis_norm a)
  refine ⟨p,?_,hp.trans (by rw [blade,onBasis])⟩
  change p.coord=Signed.reflect a
  apply Ortho.ext
  intro x
  rw [act,hyperFormula (basis_norm a),basis_inner]
  apply PiLp.ext
  intro i
  rw [Signed.mirrored]
  by_cases h : i=a
  · subst i
    simp [basis_eq]
    ring
  · simp [basis_eq,h]

private lemma fixesClock (K : Ortho) (h : Lorentz.spatialTurn K) :
    Ortho.move K (basis timeAxis)=basis timeAxis := by
  apply Mink.ext_by
  · have eq := Mink.squares (Ortho.move K (basis timeAxis))
    rw [Ortho.move_norm,basis_norm,h.2,Mink.roll_clock] at eq
    rw [Mink.roll_space]
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (spatial (Ortho.move K (basis timeAxis)))]
  · exact h.2 _

theorem wickCorrection (x : E4) :
    wickSlash x=slash x+((-Complex.I-1)*(time x:ℂ)) • gamma timeAxis := by
  unfold wickSlash slash
  conv_rhs => rw [Fin.sum_univ_castSucc,add_assoc,←add_smul]
  congr 2
  change -Complex.I * (x timeAxis:ℂ) = (x timeAxis:ℂ) + (-Complex.I-1)*(x timeAxis:ℂ)
  ring

theorem spatial (p : EuPin) (h : Lorentz.spatialTurn p.coord) :
    ∃ q : RealSpin, q.coord=Lorentz.room p.coord h ∧ q.matrix=p.matrix := by
  obtain ⟨pres,act⟩ := (euPin_iff p.val).mp p.property
  have eu (x : E4) : p.matrix.val*slash x=slash (Ortho.move p.coord x)*p.matrix.val := act x
  have clock := eu (basis timeAxis)
  rw [fixesClock p.coord h,onBasis] at clock
  refine ⟨⟨(Lorentz.room p.coord h,p.matrix),(realSpin_iff _).mpr ⟨pres,?_⟩⟩,rfl,rfl⟩
  intro x
  change p.matrix.val*wickSlash x=wickSlash (Ortho.move p.coord x)*p.matrix.val
  rw [wickCorrection,wickCorrection,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul,eu,clock,h.2]

end YM.MassiveTwoEstimates.SpinAxes
#print axioms YM.MassiveTwoEstimates.SpinAxes.reflection
#print axioms YM.MassiveTwoEstimates.SpinAxes.wickCorrection
#print axioms YM.MassiveTwoEstimates.SpinAxes.spatial
