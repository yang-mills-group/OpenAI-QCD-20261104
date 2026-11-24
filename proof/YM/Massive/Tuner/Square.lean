import YM.QCD.Sq.Axis
/-!
# Shooting not for a terminal zero
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Shooting
open QCD QCD.Sq
open scoped Topology
variable {x y : ℝ}

lemma tap_zero (h : (tap x).val=0) : x=0 := by
  by_cases hx : |x| ≤ 1
  · rwa [tapped _ hx] at h
  simpa [show |(tap x).val|=0 from by rw [h,abs_zero]] using glance _ hx

/-- Face-preserving surjection to interior points on vertical median too. -/
lemma fiber (hx : |x| < 1) (f : Twin→Twin) (hf : Continuous f)
    (h : ∀ (a:Twin) (i:Bool), |ray a i|=1 → ray (f a) i=ray a i) :
    ∃ y : Twin, tail (f y)=0 ∧ mast (f y)=x:=by
  have ht := abs_lt.mp hx
  let r := 1-|x|
  have hr : 0 < r := sub_pos.mpr hx
  let g (i : Twin) : Twin := ((f i).1, tap ((mast (f i)-x)/r))
  have hcg : Continuous g := by unfold g; fun_prop
  have he (i : Twin) (s : Bool) (hp : |ray i s|=1) : ray (g i) s=ray i s := by
    rw [← h i s hp]
    cases s with
    | false => change ray (f i) false=_; rfl
    | true =>
      change max (-1) (min 1 ((mast (f i)-x)/r)) = mast (f i)
      rcases eq_or_eq_neg_of_abs_eq (show |mast (f i)|=1 from by convert Eq.trans (congr_arg abs (h i true hp)) hp; rfl) with ha|ha
      · rw [ha, min_eq_left ((le_div_iff₀ hr).mpr ?_), max_eq_right]
        · norm_num
        · unfold r; linarith only [le_abs_self x]
      · rw [ha]
        rw [max_eq_left ((min_le_right _ _).trans ((div_le_iff₀ hr).mpr ?_))]
        unfold r; linarith only [neg_le_abs x]
  obtain ⟨i, hi, hh⟩:= beam g hcg he
  refine ⟨i, hi, sub_eq_zero.mp ((div_eq_zero_iff.mp (tap_zero hh)).resolve_right hr.ne')⟩
end YM.Massive.Shooting
#print axioms YM.Massive.Shooting.fiber
