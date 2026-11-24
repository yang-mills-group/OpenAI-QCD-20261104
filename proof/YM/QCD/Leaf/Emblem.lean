import YM.QCD.Leaf.Pot

/-! # perturbation poles in the absolute support norm, not just Cat locality in a sector
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.Emblem
open Lat Kit Lattice Wilson Finset Function Filter Metric Tree RG Cost
open Orbit Birth Flume Sparks Leaf LeafM Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder Garden Run
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f:Side}{D H: St f}{a b d h r η ξ δ ν A p C R V W E u L y F M G:ℝ}{n m B:ℕ}
-- telesc form one insertion. powers of function
lemma algebra (Z X: St f) (n:ℕ):
    (Z+X)^n= Z^n+∑ i∈range n, Z^i*X*(Z+X)^(n-1-i):=by
  induction n with
  | zero=> simp
  | succ n ih=>
    conv_lhs=> rw [pow_succ',add_mul]; lhs; rw [ih,mul_add,mul_sum]
    rw [Finset.sum_range_succ',Nat.add_sub_cancel] -- syntax replace
    simp_rw [pow_succ' Z, Nat.sub_add_eq, mul_assoc]; simp only [pow_zero,one_mul,Nat.sub_zero]; simp_rw [show ∀ i:ℕ,n-1-i=n-i-1 from fun i=>by omega]; abel

variable (hP : ∀ i:ℕ,Own f δ b B (D^i) (R*r^i))(hM: Own f δ b B H M)(he:0<δ)(hb:0 ≤ b)(hr:0≤r)(hh: r<V)(hx:0<M)(hR:0<R)(hu:R*M ≤ V-r)
include hP hM he hb hr hh hx hR hu
lemma adds (n:ℕ): Own f δ b B ((D+H)^n) (R*V^n):=by
  have hV:0<V:=hr.trans_lt hh
  induction n using Nat.strong_induction_on with
  | h n ih=>
    cases n with
    | zero=> simpa using hP 0
    | succ n=>
    rw [algebra, Nat.add_sub_cancel]
    have hp i (hi:i∈ range (n+1)): Own f δ b B (D^i*H*(D+H)^(n-i)) ((R*r^i)*M*(R*V^(n-i))) := ((hP i).meet hM he hb (by positivity) hx.le).meet (ih _ (by omega)) he hb (by positivity) (by positivity)
    have ht : Own f δ b B (∑ i∈range (n+1),D^i*H*(D+H)^(n-i)) (∑ i∈range (n+1),R*r^i*M*(R*V^(n-i))) := by
      rw [show (∑ i∈range (n+1),D^i*H*(D+H)^(n-i))=(fun Z=>∑ i∈range (n+1),(D^i*H*(D+H)^(n-i)) Z) from funext fun i=> Finset.sum_apply ..]; exact Heritage.joined _ _ hp
    refine ((hP (n+1)).plus ht).mono ?_
    let f:= ∑ i∈range (n+1),r^i*V^(n-i)
    have he (i:ℕ) : R*r^i*M*(R*V^(n-i))=(r^i*V^(n-i))*(R*M)*R:=by ring
    simp_rw [he,←sum_mul]; refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (show 0 ≤ f by unfold f; positivity)) hR.le) _) ?_
    have he:
        f*(r-V)=r^(n+1)-V^(n+1):=by simpa [f] using geom_sum₂_mul r V (n+1)
    change R*r^(n+1)+f*_ *_ ≤ _; apply le_of_eq; rw [show V^(n+1)=r^(n+1)+f*(V-r) by linarith]; ring
omit hP hM he hb hr hh hx hR hu
lemma pulseFloor (X:Sheet f)(ha:0<h) (ht:0 ≤ p) (hk:p<1) (hh: ‖notch h X‖ ≤ p): Cost.Floor ((1-p)/h) X:=by
  intro i; let Y:= -(1:ℂ) • notch h X; have he: (h:ℂ) • X= 1+Y:=by unfold Y notch; simp
  have hl: h*Cost.form X i=‖i‖^2-Cost.form (notch h X) i:=by rw [← real_form,he,add_form,identity]; unfold Y; rw [show -(1:ℂ)= ((-1:ℝ):ℂ) by norm_num,real_form]; ring
  have hm: Cost.form (notch h X) i ≤ p*‖i‖^2:= by
    apply (Complex.re_le_norm ..).trans ((norm_inner_le_norm ..).trans ?_); exact (mul_le_mul_of_nonneg_left ((leanBound _ _).trans (mul_le_mul_of_nonneg_right hh (by positivity))) (by positivity)).trans_eq (by ring)
  apply le_of_mul_le_mul_left _ ha; field_simp; linarith
end YM.QCD.Leaf.Emblem
