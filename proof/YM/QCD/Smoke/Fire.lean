import YM.QCD.Smoke.Lit

/-! # powers in a quadratic jet, no aperture loss along exponent; log. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Finset Lat Cost Run Eyrie Metric Lattice Wilson Push.Uniform
open YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.L2Operator
variable {n:Side} {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] {R : Type*} [Ring R]

-- falling
 def shove (A d : R)(F:ℕ→ R) : ℕ → R
  | 0=>0
  | n+1=>∑ j∈antidiagonal n, A^j.1*d*F j.2
lemma shoved (A d:R)(F:ℕ→R)(n): shove A d F (n+1)=A*shove A d F n + d* F n:=by
  cases n with
  | zero=> simp [shove]
  | succ n=> rw [shove,shove,Nat.sum_antidiagonal_succ,mul_sum]; simp_rw [pow_succ',mul_assoc]; simp; rw [add_comm] -- inspect
lemma shoved_sum (A d:R)(F G:ℕ→ R): shove A d (F+G)=shove A d F+shove A d G:=by
  funext i; cases i <;> simp [shove,mul_add,sum_add_distrib]
lemma burst (A d:R): (fun i:ℕ=> (A+d)^i)=(fun i=> A^i)+ shove A d (fun i=> (A+d)^i):=by
  funext i; induction i with
  | zero=> simp [shove]
  | succ n ih=>
    change _=A^(n+1)+_
    rw [shoved]; change (A+d)^n=_+_ at ih; rw [pow_succ',pow_succ',add_mul,ih,mul_add]; abel
variable {d A: X→Sheet n} {F:ℕ→ X→Sheet n}
private lemma hexSum {I:Type}[DecidableEq I]{f:I→X→Sheet n}(s:Finset I)(h:∀ i∈s, ContDiffAt ℝ ω (f i) 0): ContDiffAt ℝ ω (∑ i∈s,f i) 0:=by simpa only [← sum_fn] using ContDiffAt.sum h -- orientation
lemma smoothShove (ha:ContDiffAt ℝ ω A 0)(hd:ContDiffAt ℝ ω d 0)(hf:∀ i,ContDiffAt ℝ ω (F i) 0)(k:ℕ): ContDiffAt ℝ ω (shove A d F k) 0 := by
  cases k with | zero=> exact contDiffAt_const | succ n=> exact hexSum _ fun _ _=> ((ha.pow _).mul hd).mul (hf _)
lemma nullShove (h:d 0=0)(k:ℕ): shove A d F k 0=0:=by cases k <;> simp [shove,Finset.sum_apply,h]
lemma hazyShove (ha:ContDiffAt ℝ ω A 0)(hd:ContDiffAt ℝ ω d 0)(hf:∀ i,ContDiffAt ℝ ω (F i) 0)(h:d 0=0)(he:∀ i,F i 0=0)(k:ℕ)(x:X):blade x (shove A d F k) 0=0:=by
  cases k with
  | zero=> exact blade_const x 0
  | succ k =>
    have hx (j:ℕ×ℕ) : ContDiffAt ℝ ω (A^j.1*d) 0:= (ha.pow _).mul hd
    let Q (j:ℕ×ℕ):X→Sheet n:= A^j.1*d*F j.2
    have ht : shove A d F (k+1)=(fun x=>∑ i∈antidiagonal k,Q i x):= funext fun x=>sum_apply ..
    rw [ht,series x (F:=Q) (fun i _=> (hx i).mul (hf _))]; apply sum_eq_zero; intro i _; rw [show blade x (Q i) 0=_ from made x (f:=A^i.1*d) (hx i) (hf _), he]; simp [h]
lemma obscure (ha:ContDiffAt ℝ ω A 0)(hd:ContDiffAt ℝ ω d 0)(hf:∀ i,ContDiffAt ℝ ω (F i) 0)(h:d 0=0)(he:∀ i,F i 0=0)(hB:∀ i x,blade x (F i) 0=0)(k:ℕ):Duet 0 (shove A d F k):=by
  refine ⟨contDiffAt_const,smoothShove ha hd hf k,(nullShove h k).symm,fun x=> (blade_const ..).trans (hazyShove ha hd hf h he k x).symm,fun x y=>?_⟩
  have hF (k:ℕ):Jacobi.mixed x y (shove A d F k) 0=0:=by
    cases k with
    | zero=>rw [iter _ _ (smoothShove ha hd hf 0)]; simp [shove]
    | succ k=>
      have hx (j:ℕ×ℕ) : ContDiffAt ℝ ω (A^j.1*d) 0:= (ha.pow _).mul hd
      let Q (j:ℕ×ℕ):X→Sheet n:= A^j.1*d*F j.2
      have ht : shove A d F (k+1)=(fun x=>∑ i∈antidiagonal k,Q i x):= funext fun x=>sum_apply ..
      rw [ht,enroll x y (f:=Q) (fun i _=> (hx i).mul (hf _))]; apply sum_eq_zero; intro i _; rw [show Jacobi.mixed x y (Q i) 0=_ from rotate_area x y (hx i) (hf i.2)]; simp [hB,h,he]
  rw [hF]; rw [iter _ _ (show ContDiffAt ℝ ω (0:X→Sheet n) 0 from contDiffAt_const)]; simp
lemma approximate (P:X→Sheet n)(h:ContDiffAt ℝ ω P 0)(k:ℕ):
    let A:=fun _:X=> P 0; let a:=fun x=> P x-P 0; let T:= shove A a; let B i:= A^i
    Duet (B k+T B k+T (T B) k) (P^k):=by
  intro A d T B
  have hd:d 0=0:=by unfold d; simp
  have he : A+d=P:=by ext1 x; dsimp only [Pi.add_apply,A,d]; abel
  let F i:=P^i; have hF:F=B+T F:=by unfold B T F; nth_rw 1 [← he]; -- inspect
                                                first | rw [burst (R:=X→Sheet n) A d, he] -- broken
                                                      | exact (by simpa only [he] using! (burst (R:=X→Sheet n) A d))
  have hh : P^k=B k+T B k+T (T B) k+T (T (T F)) k:=by
    change F k=_; nth_rw 1 [hF]; rw [Pi.add_apply]; nth_rw 1 [hF]; rw [show T (B+T F)=_ from shoved_sum .., Pi.add_apply]; nth_rw 1 [hF]; rw [show T (B+T F)=_ from shoved_sum ..,shoved_sum,Pi.add_apply]; unfold T; abel
  have ha: ContDiffAt ℝ ω A 0:=contDiffAt_const; have hu : ContDiffAt ℝ ω d 0:=h.sub ha
  have hv i : ContDiffAt ℝ ω (B i) 0:=ha.pow _; have hx i : ContDiffAt ℝ ω (F i) 0:=h.pow _
  have hP:= smoothShove ha hu hv; have hi:=smoothShove ha hu hx
  have hj:= Duet.together (((hv k).add (hP k)).add (smoothShove ha hu hP k)) EventuallyEq.rfl
  have HM:= hj.add (obscure ha hu (smoothShove ha hu hi) hd (nullShove hd) (hazyShove ha hu hi hd (nullShove hd)) k); rw [add_zero] at HM; rw [hh]; exact HM
end YM.QCD.Smoke
