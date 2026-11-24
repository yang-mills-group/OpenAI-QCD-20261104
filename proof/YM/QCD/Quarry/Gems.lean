import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Enrobe
import YM.Next.STATIONARY.Joint.Gauge
import YM.QCD.Pearl.Usage
import YM.QCD.Revolve.Roots

/-!
# Odd replica of spinors. period provenance

The F Hess test must compare smaller torus Schur to a restriction of the
larger (not diagonal traces at one site). Keep signs at lifts, including
coarse descent. The common seam here at zero. Decide parity condition before
allocating the auxiliary family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Quarry
open Function Lattice Wilson Lat Flume Kit Revolve Free Finset Filter Laurent Bloch
open YM.Further.PhysicalPeriodLimitF933 Macrame Macrame.Window
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators
variable {n N : Side} {M k : ℕ}
lemma shimmering (x : Site n) (w) : shimmer 0 x w=seamPath x w:=by
  induction w generalizing x with
  | nil=> rfl
  | cons a w ih=> rw [shimmer,seamPath,ih]; unfold glint Step.used; split <;> rfl
lemma occ_rays (x : Site n) (w:Walk): shimmer 0 x w=occ x (stop 0 w):=by
  rw [shimmering]; apply mul_right_cancel₀ (scarf_ne (0:Site n) (stop x w)); rw [follows,wrap_stop x w]; exact (concord ..).symm -- count rw?

/-- pull cocycle convention big sign multiplies congruence -/
structure Quaint (G : Window n N M) (d : Site N→ℂ) : Prop where
  sign (x) : d x=1 ∨ d x= -1
  lift (x) (i:Step): glint 0 x i*d (x+i.vec)=d x* glint 0 (G.cut x) i
lemma tuning_share (h: N.val=n.val*k) (hk:Odd k) : ∃ p : Site N,tuning p=tuning (0:Site n) := by
  obtain ⟨r,hr⟩:=hk
  let w : Cover:=fun _=> -(r:ℤ)
  let P:=wrap N w
  have he : lift P=w:= lift_eq_iff.mpr ⟨rfl, fun i=> by
      have h1:2*r<N.val:=lt_of_lt_of_le (by omega : _<k) (by rw [h]; exact Nat.le_mul_of_pos_left _ n.property)
      change _ < _ * -(r:ℤ) ∧ _ * -(r:ℤ) ≤ _; omega⟩
  refine ⟨P,?_⟩; ext1 i; unfold tuning menu spacer fixed
  rw [he] 
  apply congr_arg Complex.ofReal; simp only [w,Pi.smul_apply,smul_eq_mul,lift,Pi.zero_apply,ZMod.valMinAbs_zero,Int.cast_zero,mul_zero,h,hr]; push_cast; field_simp; ring

lemma twinkle (G : Window n N M) (h: N.val=n.val*k) (hk:Odd k) : ∃ d : Site N→ℂ,Quaint G d := by
  obtain ⟨p,hp⟩:= tuning_share h hk
  let S:=scarf (0:Site n)
  let d (x : Site N): ℂ:= scarf p x / S (G.cut x)
  have hx x:d x≠0:= div_ne_zero (scarf_ne p x) (scarf_ne 0 _)
  have he (x : Site N) (w) : shimmer 0 x w*d (stop x w)=d x* shimmer 0 (G.cut x) w:=by
    have hm : G.cut (stop x w)=stop (G.cut x) w:=by rw [wrap_stop, G.port,wrap_stop]
    let Q := stop (G.cut x) w
    have hv:= follows (0:Site n) (G.cut x) w
    unfold d; rw [shimmering,shimmering,hm,← mul_div_assoc,follows,hp]
    change _/(S Q)=_/ _ *_; field_simp [show S Q ≠ 0 from scarf_ne 0 _, show S (G.cut x)≠0 from scarf_ne 0 _]; -- equality
    unfold S Q; grind
  have hh (x): d x=d 0 ∨ d x= -d 0 := by
    let w := route 0 (lift x) (1:Lattice.Order); have hv:= he 0 w
    rw [wrap_stop, show stop (0:Cover) w=lift x from route_end ..,zero_add,wrap_lift,shimmering,shimmering] at hv
    let A: ℂ:=seamPath (0:Site N) w * seamPath (G.cut 0) w
    have hA : d x=d 0*A:=by
      calc
        _ = seamPath (0:Site N) w*(seamPath 0 w*d x) := by rw [← mul_assoc,(realSeam ..).2,one_mul]
        _ = _ := by rw [hv]; unfold A; ring
    have hu : A^2=1^2:=by unfold A; rw [pow_two,pow_two, mul_mul_mul_comm,(realSeam ..).2,(realSeam ..).2];
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hu with h|h <;> simp only [h] at hA <;> simp [hA]
  refine ⟨fun i=>d i/d 0, fun i=>?_, fun i v=>?_⟩
  · cases hh i with
    | inl h=> exact Or.inl (by rw [h,div_self (hx 0)])
    | inr h=> exact Or.inr (by rw [h,neg_div,div_self (hx 0)])
  have hv:= he i [v]; simp only [shimmer,mul_one,stop] at hv; rw [← mul_div_assoc,hv]; ring

end YM.QCD.Quarry
