import YM.QCD.RP.Hop

/-!
# Positivity of Grassmann exponential over the cleared cut links

Algebraic cone (finite Clifford/exterior dimension). Includes second plane
with opposite twist. Order theta(x) x.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Function Finset Lat Lattice Grass NormedSpace
open scoped Matrix Matrix.Norms.Frobenius Kronecker Topology BigOperators

variable {n : Side} {R : Cells.Cut n} {F : ℕ}

def hit (R : Cells.Cut n) (w x : Dirac (Lamp R F)) := theta R (pass (light R) w) * pass (light R) x
lemma hit_even {p : Bool} (w x : Dirac (Lamp R F)) (h : Hom p w) (hx : Hom p x) : Plus (hit R w x) := by
  unfold Plus hit
  cases p <;> simp_all [Hom, Minus,Plus,map_mul,pass_grade,theta_grade]
lemma shuffle {p : Bool} (w x y z : Dirac (Lamp R F)) (h : Hom p w) (hx : Hom p x) :
    hit R w x * hit R y z = hit R (w*y) (x*z) := by
  rw [show hit R y z = theta R (pass (light R) y)*pass (light R) z from rfl, ← mul_assoc,((hit_even w x h hx).central _).symm.eq]
  simp only [hit,map_mul, theta_mul, mul_assoc]

/-- only need sums and homogeneous monomials. -/
inductive Matinee (R : Cells.Cut n) : Fields n F → Prop
| zero : Matinee R 0
| ray (p : Bool) (x : Dirac (Lamp R F)) (hx : Hom p x) : Matinee R (hit R x x)
| add {x y} (hx : Matinee R x) (hy : Matinee R y) : Matinee R (x+y)

lemma Matinee.times {x y : Fields n F} (h : Matinee R x) (hh : Matinee R y) : Matinee R (x*y) := by
  induction h with
  | zero => rw [zero_mul]; exact .zero
  | ray p u hp =>
    induction hh with
    | zero => rw [mul_zero]; exact .zero
    | ray q v hv => rw [shuffle u u v v hp hp]; exact .ray (p ^^ q) (u*v) (hp.mul hv)
    | add _ _ ih₁ ih₂ => rw [mul_add]; exact ih₁.add ih₂
  | add _ _ ih₁ ih₂ => rw [add_mul]; exact ih₁.add ih₂
lemma Matinee.one : Matinee R (1:Fields n F) := by
  simpa [hit,theta] using Matinee.ray (R:=R) false (1 : Dirac (Lamp R F)) (by simp [Hom,Plus])

/-- any odd square is zero. -/
lemma square_odd {A : Type*} [Fintype A] {x : Alg A} (hp : Minus x) : x*x=0 := by
  have h := Minus.slides hp x
  rw [show grade x = _ from hp,mul_neg] at h
  have he : ∀ s,coef s (x*x)=0 := fun s => neg_eq_self.mp (by simpa only [map_neg (coef s)] using congrArg (coef s) h.symm)
  rw [← write (x*x)]; simp only [he,zero_smul,sum_const_zero]

lemma arrow {x : Dirac (Lamp R F)} (hp : Minus x) : Plus (hit R x x) ∧ Matinee R (exp (hit R x x)) := by
  refine ⟨hit_even (p:=true) _ _ hp hp, ?_⟩
  rw [radius_two _ (by rw [shuffle (p:=true) x x _ _ hp hp,square_odd hp]; simp [hit])]
  exact Matinee.add Matinee.one (.ray true _ hp)
lemma panels {I : Type*} (f : I → Fields n F) (s : Finset I)
    (he : ∀ i∈s, Plus (f i) ∧ Matinee R (exp (f i))) : Plus (∑ i∈s,f i) ∧ Matinee R (exp (∑ i∈s,f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty,exp_zero]; exact ⟨by simp [Plus], .one⟩
  | @insert i s hi ih =>
    obtain ⟨hl,hp⟩ := ih (fun i hx => he _ (mem_insert_of_mem hx))
    obtain ⟨H,Q⟩ := he i (mem_insert_self ..)
    rw [sum_insert hi,algebra_exp_add (hl.central _)]; exact ⟨Hom.add (p:=false) H hl, Q.times hp⟩
lemma twain {x y : Fields n F} (h₁ : Plus x ∧ Matinee R (exp x)) (h₂ : Plus y ∧ Matinee R (exp y)) :
    Plus (x+y) ∧ Matinee R (exp (x+y)) := by
  rw [algebra_exp_add (h₂.1.central _)]; exact ⟨Hom.add (p:=false) h₁.1 h₂.1,h₁.2.times h₂.2⟩

def ketP {X : Type*} [Fintype X] (x : X) (M : Short F) (i : Wind F) := ∑ j : Wind F,M i j • psi (place x j)
def braB {X : Type*} [Fintype X] (x : X) (M : Short F) (i : Wind F) := ∑ j : Wind F,M j i • bar (place x j)
lemma litP (x : Sky R) (M : Short F) (i) : pass (light R) (ketP x M i) = ketP x.val M i := by simp only [ketP,map_sum,map_smul,pass_psi]; rfl
lemma litB (x : Sky R) (M : Short F) (i) : pass (light R) (braB x M i) = braB x.val M i := by simp only [braB,map_sum,map_smul,pass_bar]; rfl

lemma switchP (x : Site n) (M : Short F) (i) :
    theta R (ketP x M i)=braB (R.reflect x) ((-glow R.pos F)* star M) i := by
  unfold ketP braB; simp_rw [map_sum,map_smulₛₗ,theta_psi,smul_sum, Matrix.mul_apply,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    sum_smul,smul_smul, starRingEnd_apply, Matrix.neg_apply]; rw [sum_comm]; refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_; rw [mul_comm]
lemma switchB (x : Site n) (M : Short F) (i) :
    theta R (braB x M i)=ketP (R.reflect x) (star M * (-glow R.pos F)) i := by
  unfold ketP braB; simp_rw [map_sum,map_smulₛₗ,theta_bar,smul_sum, Matrix.mul_apply,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    sum_smul,smul_smul,starRingEnd_apply, Matrix.neg_apply]; rw [sum_comm]

lemma made (x y : Site n) (M N : Short F) : linkB x y (M*N) = ∑ i : Wind F, ketP y N i * braB x M i := by
  unfold linkB ketP braB; simp_rw [Matrix.mul_apply,sum_smul]
  simp_rw [mul_sum,sum_mul,mul_smul_comm,smul_mul_assoc,smul_smul]
  nth_rw 2 [sum_comm]
  apply sum_congr rfl; intro i _; exact sum_comm

lemma flex (x y : Site n) (M N : Short F) (i j) :
    braB x M i * ketP y N j = -(ketP y N j * braB x M i) := by
  apply Hom.swap (p:=true) (q:=true)
  · exact Hom.sum (fun i _ => Hom.smul (p:=true) (grade_atom _) _)
  exact Hom.sum (fun i _ => Hom.smul (p:=true) (grade_atom _) _)

local notation "a" => R.pos
lemma throughK (x : Sky R) (M : Short F) : Plus (-linkB (R.reflect x) x.val ((-glow a F * star M)*M)) ∧
    Matinee R (exp (-linkB (R.reflect x) x.val ((-glow a F * star M)*M))) := by
  have he : -linkB (R.reflect x) x.val ((-glow a F * star M)*M) = ∑ i, hit R (ketP x M i) (ketP x M i) := by
    simp_rw [made,hit,litP,switchP,flex,sum_neg_distrib]
  rw [he]; exact panels _ _ fun i _ => arrow (Hom.sum (p:=true) (fun i _ => Hom.smul (p:=true) (grade_atom _) _))
lemma throughB (x : Sky R) (M : Short F) : Plus (linkB x.val (R.reflect x) (M*(star M * (-glow a F)))) ∧
    Matinee R (exp (linkB x.val (R.reflect x) (M*(star M * (-glow a F))))) := by
  have he : linkB x.val (R.reflect x) (M*(star M * (-glow a F))) = ∑ i, hit R (braB x M i) (braB x M i) := by
    simp_rw [made,hit,litB,switchB]
  rw [he]; exact panels _ _ fun i _ => arrow (Hom.sum (p:=true) (fun i _ => Hom.smul (p:=true) (grade_atom _) _))

def small (e : Axis) (F : ℕ) := copies F (wave (lo e))
def big (e : Axis) (F : ℕ) := copies F (wave (hi e))
lemma touch_minus (M : Mat) : touch (-M) = -touch M := neg_kron ..
lemma wave_minus (M : Spike) : wave (-M) = -wave M := kron_neg ..
@[simp] lemma small_star (F) (a₁) : star (small a₁ F)=small a₁ F := by rw [small,← copies_star, wave_star, lo_star]
@[simp] lemma big_star (F) (a₁) : star (big a₁ F)=big a₁ F := by rw [big,← copies_star,wave_star, hi_star]
@[simp] lemma small_sq (F) (a₁) : small a₁ F*small a₁ F=small a₁ F := by rw [small,← copies_mul, wave_mul,lo_sq]
@[simp] lemma big_sq (F) (a₁) : big a₁ F*big a₁ F=big a₁ F := by rw [big,← copies_mul,wave_mul,hi_sq]
@[simp] lemma si₁ (F) (a₁) : glow a₁ F*small a₁ F= -small a₁ F := by rw [glow,small,lamp,← copies_mul,wave_mul,gamma_lo,wave_minus,copies_neg]
@[simp] lemma si₂ (F) (a₁) : small a₁ F*glow a₁ F= -small a₁ F := by rw [small,glow,lamp,← copies_mul,wave_mul,odd_lo,wave_minus,copies_neg]
@[simp] lemma si₃ (F) (a₁) : glow a₁ F*big a₁ F=big a₁ F := by rw [glow,big,lamp,← copies_mul,wave_mul,gamma_hi]
@[simp] lemma si₄ (F) (a₁) : big a₁ F*glow a₁ F=big a₁ F := by rw [big,glow,lamp,← copies_mul,wave_mul,even_hi]

lemma leading (x : Sky R) : let y := spans F a 1 (R.reflect x.val) x.val
    Plus y ∧ Matinee R (exp y) := by
  have h := twain (throughK x (small a F)) (throughB x (big a F))
  dsimp only [spans,down,up]; simp only [small_star,big_star,neg_mul,mul_neg,si₁,si₄,neg_neg,big_sq,small_sq,linkB_neg,sub_eq_add_neg,star_one,touch_one,mul_one] at h ⊢; exact h
lemma trailing (x : Sky R) : let y := spans F a (-1) x.val (R.reflect x.val)
    Plus y ∧ Matinee R (exp y) := by
  have h := twain (throughB x (small a F)) (throughK x (big a F))
  dsimp only [spans,down,up]; simp only [small_star,big_star,neg_mul,mul_neg,si₃,si₂,big_sq, neg_neg,small_sq,star_neg,star_one,touch_minus,touch_one,mul_one,copies_neg,linkB_neg,sub_eq_add_neg,neg_neg] at h ⊢; exact h
end YM.QCD.RP
