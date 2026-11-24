import YM.Massive.Target.Covers
import YM.QCD.Revolve.Jolt

/-! The concrete Euclidean and Lorentzian spin presentations in the massive
target have exactly two lifts over every coordinate element in their image. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinFibres
open Massive QCD QCD.Lat Matrix Mink
open scoped BigOperators

private theorem charge_ne : chargeMatrix ≠ 0 := by
  intro zero
  have h := congrArg (fun X : Spike => gamma 0 * X * gamma 2) zero
  have one : (1 : Spike) = 0 := by
    simpa only [chargeMatrix,← Matrix.mul_assoc,gamma_sq,one_mul,mul_zero,zero_mul] using h
  exact one_ne_zero one

private theorem scalarSign (S : Spikeˣ) (preserves : KeepsC S)
    (commutes : ∀ a, Commute S.val (gamma a)) : S.val = 1 ∨ S.val = -1 := by
  let z := S.val (0,0) (0,0)
  have scalar : S.val = z • (1 : Spike) := Revolve.scalar_spin commutes
  have c : (z*z) • chargeMatrix = chargeMatrix := by
    change S.val * chargeMatrix * S.val.transpose = chargeMatrix at preserves
    simpa only [scalar,transpose_smul,transpose_one,Matrix.smul_mul,one_mul,
      Matrix.mul_smul,mul_one,smul_smul] using preserves
  have hz : z*z=1 := by
    have zero : (z*z-1) • chargeMatrix = 0 := by rw [sub_smul,c,one_smul,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp zero).resolve_right charge_ne)
  have prod : (z-1)*(z+1)=0 := by linear_combination hz
  rcases mul_eq_zero.mp prod with h | h
  · left
    simpa only [sub_eq_zero.mp h,one_smul] using scalar
  · right
    have minus : z = -1 := by linear_combination h
    simpa only [minus,neg_one_smul] using scalar

private theorem undo {S T : Spikeˣ}
    (h : (T⁻¹*S).val=1 ∨ (T⁻¹*S).val= -1) : S=T ∨ S= -T := by
  have cancel : T.val * (T⁻¹).val = 1 := T.val_inv
  rcases h with h | h
  · left
    apply Units.ext
    simpa only [Units.val_mul,← Matrix.mul_assoc,cancel,one_mul,mul_one]
      using congrArg (T.val * ·) h
  · right
    apply Units.ext
    simpa only [Units.val_mul,← Matrix.mul_assoc,cancel,one_mul,mul_neg,mul_one,Units.val_neg]
      using congrArg (T.val * ·) h

private theorem slashBasis (a : Axis) : slash (basis a) = gamma a := by
  classical
  simp [slash,basis_eq,ite_smul]

private theorem wickBasis (a : SpaceAxis) : wickSlash (basis a.castSucc) = gamma a.castSucc := by
  classical
  have zero : timeAxis ≠ a.castSucc := (Fin.castSucc_ne_last a).symm
  simp [wickSlash,time,basis_eq,ite_smul,zero]

private theorem wickTime : wickSlash (basis timeAxis) = -Complex.I • gamma timeAxis := by
  classical
  have zero (i : SpaceAxis) : i.castSucc ≠ timeAxis := Fin.castSucc_ne_last i
  simp [wickSlash,time,basis_eq,zero]

theorem euFiber (p q : EuPin) (h : p.coord=q.coord) : p=q ∨ p.matrix = -q.matrix := by
  let r := q⁻¹*p
  have coord : r.coord=1 := by change q.coord⁻¹*p.coord=1; rw [h,inv_mul_cancel]
  obtain ⟨pres,act⟩ := (euPin_iff r.val).mp r.property
  have spin (a : Axis) : Commute r.matrix.val (gamma a) := by
    have eq := act (basis a)
    change r.matrix.val * slash (basis a) = slash (Ortho.move r.coord (basis a)) * r.matrix.val at eq
    change r.matrix.val * gamma a = gamma a * r.matrix.val
    simpa only [coord,Ortho.move_one,slashBasis] using eq
  obtain same | opposite := undo (S:=p.matrix) (T:=q.matrix) (scalarSign r.matrix pres spin)
  · exact Or.inl (Subtype.ext (Prod.ext h same))
  · exact Or.inr opposite

theorem minkFiber (p q : RealSpin) (h : p.coord=q.coord) : p=q ∨ p.matrix = -q.matrix := by
  let r := q⁻¹*p
  have coord : r.coord=1 := by change q.coord⁻¹*p.coord=1; rw [h,inv_mul_cancel]
  obtain ⟨pres,act⟩ := (realSpin_iff r.val).mp r.property
  have spin (a : Axis) : Commute r.matrix.val (gamma a) := by
    refine Fin.lastCases ?_ (fun b => ?_) a
    · have eq := act (basis timeAxis)
      change r.matrix.val * wickSlash (basis timeAxis) =
        wickSlash (r.coord.act (basis timeAxis)) * r.matrix.val at eq
      rw [coord,Lorentz.act_one,wickTime,Matrix.mul_smul,Matrix.smul_mul] at eq
      exact (smul_right_injective _ (neg_ne_zero.mpr Complex.I_ne_zero)) eq
    · have eq := act (basis b.castSucc)
      change r.matrix.val * wickSlash (basis b.castSucc) =
        wickSlash (r.coord.act (basis b.castSucc)) * r.matrix.val at eq
      change r.matrix.val * gamma b.castSucc = gamma b.castSucc * r.matrix.val
      simpa only [coord,Lorentz.act_one,wickBasis] using eq
  obtain same | opposite := undo (S:=p.matrix) (T:=q.matrix) (scalarSign r.matrix pres spin)
  · exact Or.inl (Subtype.ext (Prod.ext h same))
  · exact Or.inr opposite

private theorem preservesNeg {S : Spikeˣ} (h : KeepsC S) : KeepsC (-S) := by
  simpa only [KeepsC,Units.val_neg,transpose_neg,neg_mul,mul_neg,neg_neg] using h

theorem euBoth (p : EuPin) : ∃ q : EuPin, p.coord=q.coord ∧ q.matrix = -p.matrix := by
  obtain ⟨pres,act⟩ := (euPin_iff p.val).mp p.property
  refine ⟨⟨(p.coord,-p.matrix), (euPin_iff _).mpr ⟨preservesNeg pres,fun x => ?_⟩⟩,rfl,rfl⟩
  change (-p.matrix).val * _ = _ * (-p.matrix).val
  simp only [Units.val_neg,neg_mul,mul_neg]
  exact congrArg Neg.neg (act x)

theorem minkBoth (p : RealSpin) : ∃ q : RealSpin, p.coord=q.coord ∧ q.matrix = -p.matrix := by
  obtain ⟨pres,act⟩ := (realSpin_iff p.val).mp p.property
  refine ⟨⟨(p.coord,-p.matrix), (realSpin_iff _).mpr ⟨preservesNeg pres,fun x => ?_⟩⟩,rfl,rfl⟩
  change (-p.matrix).val * _ = _ * (-p.matrix).val
  simp only [Units.val_neg,neg_mul,mul_neg]
  exact congrArg Neg.neg (act x)

end YM.MassiveTwoEstimates.SpinFibres
#print axioms YM.MassiveTwoEstimates.SpinFibres.euBoth
#print axioms YM.MassiveTwoEstimates.SpinFibres.euFiber
#print axioms YM.MassiveTwoEstimates.SpinFibres.minkBoth
#print axioms YM.MassiveTwoEstimates.SpinFibres.minkFiber
