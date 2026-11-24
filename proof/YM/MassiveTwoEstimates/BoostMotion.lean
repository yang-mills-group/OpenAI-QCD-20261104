import YM.MassiveTwoEstimates.BoostBasis

/-! Intertwining with every actual Lorentz boost, including the transverse
spin components and negative as well as positive rapidities. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.BoostMotion
open Massive Mink Matrix QCD.Lat BoostRotor BoostBasis SpinClifford Finset
open scoped BigOperators Matrix.Norms.Frobenius InnerProductSpace

def space (z : Space3) : Spike := ∑ i,(z i:ℂ) • gamma i.castSucc

theorem spaceAdd (z y : Space3) : space (z+y)=space z+space y := by
  change (∑ i, ((z i+y i:ℝ):ℂ) • gamma i.castSucc)=_
  simp only [space,Complex.ofReal_add,add_smul,sum_add_distrib]

theorem spaceSmul (r : ℝ) (z : Space3) : space (r • z)=(r:ℂ) • space z := by
  change (∑ i, ((r*z i:ℝ):ℂ) • gamma i.castSucc)=_
  simp only [space,Complex.ofReal_mul,Finset.smul_sum,smul_smul]

theorem slice (z : Space3) : slash (position z 0)=space z := by
  unfold slash
  rw [Fin.sum_univ_castSucc]
  change (∑ i : SpaceAxis, ((position z 0 i.castSucc:ℝ):ℂ) • gamma i.castSucc) +
    ((time (position z 0):ℝ):ℂ) • gamma timeAxis = _
  rw [time_position,Complex.ofReal_zero,zero_smul,add_zero]
  simp [space,position]

theorem wick (z : Space3) (t : ℝ) : wickSlash (position z t)=space z+(t:ℂ) • clockM := by
  unfold wickSlash space
  simp [position,time,clockM,clock,smul_smul,mul_comm]

private theorem anti (z y : Space3) (h : inner ℝ z y=0) :
    space z*space y= -(space y*space z) := by
  have ht := polarized (position z 0) (position y 0)
  rw [Mink.pairing] at ht
  apply eq_neg_of_add_eq_zero_left
  simpa [slice,h] using ht

private theorem clockAnti (z : Space3) : clock*space z= -(space z*clock) := by
  have ht := polarized (basis timeAxis) (position z 0)
  have hs : slash (basis timeAxis)=clock := by classical simp [slash,basis_eq,ite_smul,clock]
  have h : inner ℝ (basis timeAxis) (position z 0)=0 := by rw [basis_inner]; exact time_position _ _
  apply eq_neg_of_add_eq_zero_left
  simpa [h,hs,slice] using ht

theorem transverse (e : Ray) (r : ℝ) (z : Space3) (orthogonal : inner ℝ e.val z=0) :
    conjugate e r (space z)=space z := by
  have a : axis e*space z= -(space z*axis e) := by
    simpa [axis,dir,slice] using anti _ _ orthogonal
  have g : generator e*space z=space z*generator e := by
    rw [generator,Matrix.smul_mul,Matrix.mul_smul]
    congr 1
    calc
      _ = -(axis e*space z)*clock := by
        rw [Matrix.mul_assoc,clockAnti,mul_neg,neg_mul,Matrix.mul_assoc]
      _ = _ := by rw [a,neg_neg,Matrix.mul_assoc]
  have m : mat e r*space z=space z*mat e r := by
    simp only [mat,binomial,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,g]
  rw [conjugate,m,Matrix.mul_assoc,matInv,mul_one]

private theorem fields (e : Ray) (z : Space3) (s t : ℝ) :
    wickSlash (position (z+s • e.val) t)=space z+(s:ℂ) • axis e+(t:ℂ) • clockM := by
  rw [wick,spaceAdd,spaceSmul,axis,dir,slice]

theorem action (e : Ray) (r : ℝ) (x : E4) :
    conjugate e r (wickSlash x)=wickSlash (e.shift r x) := by
  let s := e.along x
  let t := time x
  let z := spatial x-s • e.val
  have orthogonal : inner ℝ e.val z=0 := by
    simp [z,s,Ray.along,inner_sub_right,inner_smul_right,
      e.property,real_inner_comm e.val]
  have before : x=position (z+s • e.val) t := by
    dsimp [z,t]; rw [sub_add_cancel,position_eta]
  have after : e.shift r x=position
      (z+(Real.cosh r*s+Real.sinh r*t) • e.val) (Real.sinh r*s+Real.cosh r*t) := by
    apply Mink.ext_by
    · rw [Ray.newSpace,spatial_position]; dsimp [z,s,t]; module
    · rw [Ray.newClock,time_position]; dsimp [s,t]; ring
  conv_lhs => rw [before,fields]
  rw [after,fields,BoostBasis.add,BoostBasis.add,BoostBasis.smul,BoostBasis.smul,
    transverse e r z orthogonal,longitudinal,temporal]
  push_cast
  module

theorem intertwines (e : Ray) (r : ℝ) (x : E4) :
    mat e r*wickSlash x=wickSlash (e.shift r x)*mat e r := by
  rw [←action,conjugate,Matrix.mul_assoc (mat e r*wickSlash x),
    show mat e (-r)*mat e r=1 from by simpa using matInv e (-r),mul_one]

def point (e : Ray) (r : ℝ) : RealSpin :=
  ⟨(e.boost r,unit e r),(realSpin_iff _).mpr ⟨preserves e r,intertwines e r⟩⟩

theorem continuousPoint (e : Ray) : Continuous (point e) := by
  have u : Continuous (unit e) := Units.continuous_iff.mpr
    ⟨continuousMatrix e,(continuousMatrix e).comp continuous_neg⟩
  exact (e.continuousBoost.prodMk u).subtype_mk _

theorem boost (a : SpaceAxis) : ∃ p, RealSpin.Path a p := by
  let e := Ray.fromAxis a
  refine ⟨point e,?_,continuousPoint e,fun _=>rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact e.start
  · apply Units.ext
    change mat e 0=1
    simp [mat,binomial]

end YM.MassiveTwoEstimates.BoostMotion
#print axioms YM.MassiveTwoEstimates.BoostMotion.action
#print axioms YM.MassiveTwoEstimates.BoostMotion.boost
