import YM.MassiveTwoEstimates.SpinClifford

/-! Explicit spinor lifts of real hyperplane reflections in four dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.SpinReflection
open Massive QCD.Lat SpinClifford Matrix
open scoped BigOperators InnerProductSpace Kronecker

private theorem fiveT : g5.transpose = g5 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [g5,sz,Matrix.one_apply]

private theorem chargeFive : g5*chargeMatrix = chargeMatrix*g5 := by
  unfold chargeMatrix
  have rev (a : Axis) : g5*gamma a = -(gamma a*g5) := by rw [five,neg_neg]
  calc
    _ = (g5 * gamma 0) * gamma 2 := (Matrix.mul_assoc ..).symm
    _ = gamma 0 * (gamma 2*g5) := by rw [rev 0,neg_mul,Matrix.mul_assoc,rev 2,mul_neg,neg_neg]
    _ = _ := (Matrix.mul_assoc ..).symm

def blade (u : E4) : Spike := -Complex.I • (slash u*g5)

private theorem squareOne {u : E4} (unit : ‖u‖=1) : slash u * slash u = 1 := by
  simpa [unit] using square u

private theorem reversed (u : E4) : g5*slash u = -(slash u*g5) := by rw [fiveSlash,neg_neg]

theorem involution {u : E4} (unit : ‖u‖=1) : blade u * blade u = 1 := by
  have product : (slash u*g5)*(slash u*g5) = -(1:Spike) := by
    calc
      _ = slash u * ((g5*slash u)*g5) := by simp only [Matrix.mul_assoc]
      _ = -((slash u*slash u)*(g5*g5)) := by
        rw [reversed,neg_mul,mul_neg]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [squareOne unit,g5_sq,mul_one]
  simp only [blade,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul_neg,
    Complex.I_mul_I,product,neg_one_smul,neg_neg]

def lift {u : E4} (unit : ‖u‖=1) : Spikeˣ :=
  ⟨blade u,blade u,involution unit,involution unit⟩

private theorem chargeBlade (u : E4) : blade u * chargeMatrix =
    chargeMatrix * (blade u).transpose := by
  have odd : g5*(slash u).transpose = -((slash u).transpose*g5) := by
    simpa only [transpose_mul,transpose_neg,fiveT] using congrArg Matrix.transpose (fiveSlash u)
  unfold blade
  rw [Matrix.smul_mul,transpose_smul,transpose_mul,fiveT,Matrix.mul_smul]
  congr 1
  calc
    _ = (slash u*chargeMatrix)*g5 := by rw [Matrix.mul_assoc,chargeFive,Matrix.mul_assoc]
    _ = _ := by rw [chargeSlash,neg_mul,Matrix.mul_assoc,odd,mul_neg]

theorem preserves {u : E4} (unit : ‖u‖=1) : KeepsC (lift unit) := by
  change blade u * chargeMatrix * (blade u).transpose = chargeMatrix
  rw [chargeBlade,Matrix.mul_assoc,←transpose_mul,involution unit,transpose_one,mul_one]

/-- Clifford multiplication implements the Euclidean reflection of vectors,
with the coordinate and spin normalizations in the target. -/
theorem intertwines {u : E4} (unit : ‖u‖=1) (x : E4) :
    blade u * slash x = slash (x-(2 * inner ℝ u x) • u) * blade u := by
  let d : ℂ := ((2 * inner ℝ u x : ℝ) : ℂ)
  have ant : slash x * slash u - d • (1:Spike) = -(slash u * slash x) := by
    have h := polarized u x
    change slash u * slash x + slash x * slash u = d • (1:Spike) at h
    rw [←h]
    abel
  rw [blade,Matrix.smul_mul,Matrix.mul_smul]
  congr 1
  rw [slashSub,slashSmul]
  change (slash u*g5)*slash x = (slash x - d • slash u)*(slash u*g5)
  calc
    _ = -(slash u*slash x)*g5 := by rw [Matrix.mul_assoc,reversed,mul_neg,neg_mul,Matrix.mul_assoc]
    _ = (slash x*slash u - d • (1:Spike))*g5 := by rw [ant]
    _ = _ := by rw [← Matrix.mul_assoc,sub_mul _ _ (slash u),Matrix.smul_mul,squareOne unit]

def hyper (u : E4) := (ℝ ∙ u)ᗮ.reflection

theorem hyperFormula {u : E4} (unit : ‖u‖=1) (x : E4) :
    hyper u x = x-(2*inner ℝ u x) • u := by
  rw [hyper,Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
  simp [unit,real_inner_comm x u,two_smul]
  module

theorem unitMirror {u : E4} (unit : ‖u‖=1) :
    ∃ p : EuPin, p.matrix.val = blade u ∧ ∀ x, Ortho.move p.coord x = hyper u x := by
  obtain ⟨A,hA⟩ := OS.Ground.columns (hyper u)
  let S := lift unit
  have h : (A,S) ∈ euPinSubgroup := (euPin_iff _).mpr ⟨preserves unit,fun x => by
    change blade u * slash x = slash (Ortho.move A x) * blade u
    rw [hA,hyperFormula unit,intertwines unit]⟩
  exact ⟨⟨(A,S),h⟩,rfl,hA⟩

/-- A product of the explicit unit mirrors lifts every orthogonal map. -/
theorem generatedLift (P : EuPin → Prop) (one : P 1)
    (mul : ∀ p q, P p → P q → P (p*q))
    (mirror : ∀ u : E4, ‖u‖=1 → ∀ p : EuPin, p.matrix.val=blade u → P p)
    (A : Ortho) : ∃ p : EuPin, p.coord=A ∧ P p := by
  have single (v : E4) : ∃ p : EuPin, P p ∧ ∀ x, Ortho.move p.coord x = hyper v x := by
    by_cases zero : v=0
    · subst v
      refine ⟨1,one,fun x => ?_⟩
      change Ortho.move 1 x = _
      rw [Ortho.move_one,hyper,Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
      simp
    let u := ‖v‖⁻¹ • v
    have hn : ‖u‖=1 := by simp [u,norm_smul,zero]
    obtain ⟨p,hm,hp⟩ := unitMirror hn
    have sp : ℝ ∙ u = ℝ ∙ v := Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr zero))) v
    exact ⟨p,mirror u hn p hm,fun x => (hp x).trans (congrArg (fun V : Submodule ℝ E4 => Vᗮ.reflection x) sp)⟩
  have chain (l : List E4) : ∃ p : EuPin, P p ∧ ∀ x, Ortho.move p.coord x = (l.map hyper).prod x := by
    induction l with
    | nil => exact ⟨1,one,fun x => Ortho.move_one x⟩
    | cons v l ih =>
      obtain ⟨p,ps,hp⟩ := single v
      obtain ⟨q,qs,hq⟩ := ih
      refine ⟨p*q,mul p q ps qs,fun x => ?_⟩
      change Ortho.move (p.coord*q.coord) x = _
      rw [Ortho.move_mul,hq,hp]
      rfl
  obtain ⟨l,_,hl⟩ := (Ortho.motion A).reflections_generate_dim
  obtain ⟨p,ps,hp⟩ := chain l
  refine ⟨p,Ortho.ext _ _ (fun x => ?_),ps⟩
  rw [hp]
  exact (congrArg (fun f : E4 ≃ₗᵢ[ℝ] E4 => f x) hl).symm

theorem euclidean : Function.Surjective EuPin.coord := by
  intro A
  obtain ⟨p,hp,_⟩ := generatedLift (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial) A
  exact ⟨p,hp⟩

private lemma bladeHermitian (u : E4) : star (blade u)=blade u := by
  have sr : star (slash u)=slash u := by simp [slash,star_smul]
  rw [blade,star_smul,star_neg,Complex.star_def,Complex.conj_I,neg_neg,star_mul,g5_star,sr,reversed]
  simp only [smul_neg,neg_smul]

theorem unitary (p : EuPin) : p.matrix.val ∈ _root_.unitary Spike := by
  have chosen := generatedLift (fun q : EuPin => q.matrix.val ∈ _root_.unitary Spike)
    (_root_.unitary Spike).one_mem
    (fun _ _ hu hv => (_root_.unitary Spike).mul_mem hu hv)
    (fun u hu q hq => by
      rw [hq]
      exact ⟨by rw [bladeHermitian,involution hu],by rw [bladeHermitian,involution hu]⟩) p.coord
  obtain ⟨q,hq,hu⟩ := chosen
  rcases SpinFibres.euFiber p q hq.symm with rfl | opposite
  · exact hu
  · rw [opposite,Units.val_neg]
    exact ⟨by simpa only [star_neg,neg_mul_neg] using hu.1,
      by simpa only [star_neg,neg_mul_neg] using hu.2⟩

end YM.MassiveTwoEstimates.SpinReflection
#print axioms YM.MassiveTwoEstimates.SpinReflection.unitMirror
#print axioms YM.MassiveTwoEstimates.SpinReflection.euclidean
#print axioms YM.MassiveTwoEstimates.SpinReflection.unitary
