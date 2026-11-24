import YM.QCD.Calm.Bolt
import YM.Push.LOCAL_SPLITTING.Orientation
/-! # Strut budgets vector. via local extension moves -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Julius
open Function Lattice Wilson RG Source Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}
private def movedDirs (s : Signed) (b : Site n) (A : Directions G n) : LR G n :=
  ((fun e => if s.flip e.2 then 0 else A (affine s b e.1, s.perm e.2)),
    fun e => if s.flip e.2 then -A (affine s b e.1-step (s.perm e.2), s.perm e.2) else 0)

private theorem pull_increment (s : Signed) (b : Site n) (U : Config G n) (A : Directions G n) (t : ℝ) :
    pull s b (increment U (t • A)) = mix (pull s b U) (t • movedDirs s b A) := by
  ext i
  simp only [pull,Lattice.Step.rotate, Lattice.Step.read,Lattice.Step.used,posDir,Bool.false_xor, mix, increment, movedDirs]
  split <;> simp [*,Work.F03.exp_neg_color]

private theorem pull_jets {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (s : Signed) (b : Site n) (U : Config G n) (f : Config G n → Y) (l : List (Directions G n)) :
    leftDerivs (f ∘ pull s b) l U = mixJets f (l.map (movedDirs s b)) (pull s b U) := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp [mixJets,leftDerivs,ih,pull_increment]

private theorem dir_price (B : BudgetPoint) (s : Signed) (b o : Site n) (V : Config G n) (p : Directions G n)
    (h : B.dirBound (turnSites s b o) p) :
    let D (A : Directions G n) := ∀ l, ‖A l‖ ≤ (2:ℝ)^B.power * (B.threshold * (1+(separation l.1 o : ℝ))^B.power)
    D (movedDirs s b p).1 ∧ D (rotateRight V (movedDirs s b p).2) := by
  dsimp only
  constructor
  · intro l
    dsimp only [movedDirs]; split
    · rw [norm_zero]; positivity [B.threshold_pos]
    have he := h (turnSites s b l.1,s.perm l.2)
    simp only [turn_sep] at he; exact he.trans (le_mul_of_one_le_left (by positivity [B.threshold_pos]) (one_le_pow₀ (by norm_num)))
  rintro ⟨x,i⟩; rw [rotateRight, G.norm_adjoint]; dsimp only [movedDirs]; split
  · rw [norm_neg]
    let q := turnSites s b x-step (s.perm i)
    have h1 : separation q (turnSites s b o) ≤ 1+separation x o := by
      apply (separation_triangle q (turnSites s b x) _).trans
      rw [turn_sep, separation, show q - turnSites s b x = - step (s.perm i) by dsimp [q]; abel, pdist_neg]
      exact Nat.add_le_add_right (pdist_step _) _
    refine (h (q,s.perm i)).trans ?_
    rw [mul_left_comm (2^B.power), ← mul_pow]; apply mul_le_mul_of_nonneg_left _ B.threshold_pos.le
    apply pow_le_pow_left₀ (by positivity)
    change (1:ℝ)+separation q (turnSites s b o) ≤ 2*(1+(separation x o : ℝ))
    exact_mod_cast (show 1+separation q (turnSites s b o) ≤ 2*(1+separation x o) by omega)
  rw [norm_zero]; positivity [B.threshold_pos]

private theorem sum_price {ι Y : Type*} [NormedAddCommGroup Y] (l : List ι) (f : ι → Y) {c : ℝ} (hf : ∀ i∈l, ‖f i‖ ≤ c) :
    ‖(l.map f).sum‖ ≤ (l.length : ℝ)*c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (_ * c) c]
    exact (norm_add_le ..).trans (add_le_add (hf i (by simp)) (ih fun j hj => hf j (by simp [hj])))


variable {B:BudgetPoint}{o:Site n}{a:ℝ}{Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]{f:Config G n→ Y}
theorem budgetX (U:Config G n) (h:Chart B.order f U) (hc:∀ l: List (Directions G n), l.length ≤B.order→ (∀ v∈l,B.dirBound o v)→ ‖leftDerivs f l U‖≤a) (l : List (Directions G n)) (hl : l.length ≤ B.order)
    (r : ℝ) (hr : 0 < r)
    (hd : ∀ v∈l, ∀ e, ‖v e‖ ≤ r*(B.threshold * (1+(separation e.1 o : ℝ))^B.power)) :
    ‖leftDerivs f l U‖ ≤ r^l.length * a := by
  let l' := l.map (r⁻¹ • ·)
  have h' : ‖leftDerivs f l' U‖ ≤ a := by
    apply hc l' (by simpa [l'])
    simp only [l',List.forall_mem_map]
    intro v hv e; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
    exact (mul_le_mul_of_nonneg_left (hd _ hv e) (inv_pos.mpr hr).le).trans_eq (by simp [← mul_assoc,hr.ne'])
  rw [show l = l'.map (r • ·) from Eq.symm (by simp [l',List.map_map,comp_def,smul_smul, hr.ne']),
    left_homogeneous l' h (by simpa [l'] using hl), norm_smul, Real.norm_of_nonneg (pow_pos hr _).le]
  simp only [List.length_map]; exact mul_le_mul_of_nonneg_left h' (pow_pos hr _).le


lemma sails (U:Config G n)(s:Signed)(b:Site n) (h:Chart B.order f (pull s b U))(hc:∀ l:List (Directions G n), l.length ≤B.order→(∀ v∈l,B.dirBound o v)→‖leftDerivs f l (pull s b U)‖≤ a)(ha:0≤a)(l:List (Directions G n))(hl:l.length≤B.order)(hD:∀ v∈l,B.dirBound (turnSites s b o) v) : ‖leftDerivs (f ∘ pull s b) l U‖≤turnCost B.order B.power*a:=by
  let r := (2:ℝ)^B.power
  let V := pull s b U
  let Q := l.map (movedDirs s b)
  let D (A : Directions G n) := ∀ e, ‖A e‖ ≤ r*(B.threshold * (1+(separation e.1 o : ℝ))^B.power)
  have he := convert_mem V D Q (by simp only [Q,List.forall_mem_map]; exact fun p hp => dir_price B s b o V p (hD p hp))
  have hj (q) (hq : q∈convertOrder V Q) : ‖leftDerivs f q V‖ ≤ r^l.length*a := by
    have heq : q.length = l.length := (he q hq).1.trans (List.length_map _)
    rw [← heq]; exact budgetX V h hc q (heq.trans_le hl) r (by positivity) (he q hq).2
  have hs : ∀ p∈Q, ∀ q∈Q, ∀ i, p.1 i = 0 ∨ q.2 i = 0 := by
    simp only [Q,List.forall_mem_map]; intro p _ q _ i; dsimp only [movedDirs]; split <;> simp_all
  rw [pull_jets s b, mix_convert V Q f hs h ((List.length_map _).trans_le hl)]
  apply (sum_price (convertOrder V Q) _ hj).trans
  simp only [convert_length,List.length_map,Q,Nat.cast_pow,Nat.cast_ofNat,← mul_assoc, r,← mul_pow,turnCost]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))) hl) ha
end YM.Push.Local.Julius
