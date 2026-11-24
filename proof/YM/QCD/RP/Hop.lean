import YM.QCD.RP.Sky

/-!
# Local form of the Wilson bilinear and its transformation at a plane
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lattice Wilson Grass Lat NormedSpace Function Finset
open scoped Matrix.Norms.Frobenius Matrix Kronecker BigOperators Topology

variable {X : Type*} [Fintype X] {F : ℕ} {n : Side}

abbrev Short (F : ℕ) := Matrix (Wind F) (Wind F) ℂ
abbrev Press (X : Type*) (F : ℕ) := Dirac ((X × Fiber) × Flavor F)

/-- Row x, column y. Already sign in `form`. -/
def linkB (x y : X) (M : Short F) : Press X F := ∑ i,∑ j,M i j • (psi (place y j)*bar (place x i))
lemma linkB_even (x y : X) (M : Short F) : Grass.Plus (linkB x y M) := by
  simp only [Grass.Plus,linkB,map_sum,map_smul,map_mul,psi,bar,grade_atom,neg_mul_neg]
lemma linkB_add (x y : X) (M N : Short F) : linkB x y (M+N)=linkB x y M+linkB x y N := by simp [linkB,add_smul,sum_add_distrib]
lemma linkB_neg (x y : X) (M : Short F) : linkB x y (-M) = - linkB x y M := by simp [linkB]
lemma linkB_smul (x y : X) (M : Short F) (c : ℂ) : linkB x y (c • M)=c • linkB x y M := by simp [linkB,smul_sum,smul_smul]
@[fun_prop] lemma linkB_cont (x y : X) : Continuous (linkB x y (F:=F)) := by unfold linkB; fun_prop
lemma passB {R : Cells.Cut n} (x y : Sky R) (M : Short F) :
    pass (light R) (linkB x y M)=linkB x.val y.val M := by simp only [linkB,map_sum,map_smul,map_mul,pass_psi,pass_bar]; rfl

lemma groups (F : ℕ) (e : Equiv.Perm (Site n)) (B : Site n → Bundle) :
    form (copies F (rides e B))=∑ x, linkB x (e x) (copies F (B x)) := by
  unfold form; rw [placed_sum]
  apply sum_congr rfl; intro x _
  unfold linkB; apply sum_congr rfl; intro i _
  rw [placed_sum,sum_eq_single (e x)]
  · simp only [placed,if_true]
  · intro y _ hy; simp only [placed, Ne.symm hy,ite_false,zero_smul,sum_const_zero]
  simp

lemma theta_B (R : Cells.Cut n) (x y : Site n) (M : Short F) :
    theta R (linkB x y M)=linkB (R.reflect y) (R.reflect x) (glow R.pos F * star M * glow R.pos F) := by
  unfold linkB
  simp_rw [map_sum, map_smulₛₗ, theta_mul,theta_psi,theta_bar]
  let L := glow R.pos F
  let f := fun (i j u v : Wind F) => (L u j * star (M i j) * L i v) •
    (psi (place (R.reflect x) v)*bar (place (R.reflect y) u))
  have hh (i j) : star (M i j) • ((∑ t : Wind F, (-L i t) • psi (place (R.reflect x) t)) *
      ∑ z : Wind F, (-L z j) • bar (place (R.reflect y) z)) = ∑ u,∑ v,f i j u v := by
    rw [mul_sum]; simp_rw [sum_mul, smul_mul_assoc, mul_smul_comm, smul_sum, smul_smul]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    unfold f; congr 1; ring
  change ∑ i, ∑ j, star (M i j) • ((∑ t : Wind F, (-L i t) • psi (place (R.reflect x) t)) *
      ∑ z : Wind F, (-L z j) • bar (place (R.reflect y) z)) = _
  have hr (u v : Wind F) : (glow R.pos F * star M * glow R.pos F) u v •
      (psi (place (R.reflect x) v)*bar (place (R.reflect y) u)) = ∑ i,∑ j, f i j u v := by
    simp_rw [Matrix.mul_apply, Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply, sum_mul,sum_smul]; rfl
  simp_rw [hh, hr]
  have hu {I : Type} [Fintype I] (g : I → I → I → I → Fields n F) :
      ∑ i,∑ j, ∑ u,∑ v, g i j u v = ∑ u,∑ v,∑ i,∑ j,g i j u v := by
    have H := sum_comm (s:=univ) (t:=univ) (f:=fun (i j : I × I) => g i.1 i.2 j.1 j.2)
    simpa only [Fintype.sum_prod_type] using H
  exact hu f

lemma copies_neg {A : Type*} (F : ℕ) (M : Matrix A A ℂ) : copies F (-M) = - copies F M := by ext i j; by_cases h : i.2 = j.2 <;> simp [copies,Matrix.blockDiagonal_apply,h]
lemma copies_add {A : Type*} (F : ℕ) (M N : Matrix A A ℂ) : copies F (M+N)=copies F M + copies F N := Matrix.blockDiagonal_add
  (fun _ => M) (fun _ => N)
lemma copies_smul {A : Type*} (F : ℕ) (M : Matrix A A ℂ) (c : ℂ) : copies F (c • M)=c • copies F M := by ext i j; simp [copies,Matrix.blockDiagonal_apply]

def bank (m : ℝ) (F : ℕ) (x : X) : Press X F := linkB x x ((m:ℂ) • 1)
lemma theta_bank (R : Cells.Cut n) (m : ℝ) (F : ℕ) (x : Site n) : theta R (bank m F x)=bank m F (R.reflect x) := by
  rw [bank,theta_B]; simp [star_smul,star_one,Matrix.mul_smul,Matrix.smul_mul,mul_one,glow_sq,bank]
lemma banker (F : ℕ) (m : ℝ) : form (copies F ((m:ℂ) • (1 : Sheet n))) = ∑ x : Site n, bank m F x := by
  rw [← ridden,ride_smul,groups]
  simp only [Pi.smul_apply,Equiv.refl_apply,copies_smul,copies_one]; rfl

def down (F : ℕ) (a : Axis) (T : Mat) := copies F (wave (lo a)*touch T)
def up (F : ℕ) (a : Axis) (T : Mat) := copies F (wave (hi a)*touch (star T))

/-- Coupling for one link. -/
def spans (F : ℕ) (a : Axis) (T : Mat) (x y : X) := - linkB x y (down F a T) - linkB y x (up F a T)
lemma spans_even (F : ℕ) (a : Axis) (T : Mat) (x y : X) : Grass.Plus (spans F a T x y) := by
  simp only [Grass.Plus,spans,map_sub,map_neg, (show ∀ (x y : X) (V : Short F), grade (linkB x y V)=_ from linkB_even)] -- check
@[fun_prop] lemma continuous_spans (F : ℕ) (a : Axis) (x y : X) : Continuous (fun T : Mat => spans F a T x y) := by
  unfold spans up down; fun_prop
lemma surface {R : Cells.Cut n} (F : ℕ) (a : Axis) (T : Mat) (x y : Sky R) :
    pass (light R) (spans F a T x y)=spans F a T x.val y.val := by simp only [spans,map_sub,map_neg,passB]

def hopTerm (C : Lat.Cut n F) (U : Grid n) (x : Site n) (a : Axis) : Fields n F :=
  spans F a (thread C.t U a x) x (x+step a)
lemma bridge_basis (C : Lat.Cut n F) (U : Grid n) (a : Axis) :
    form (copies F (1-singleHop C.t U a)) = (∑ x : Site n, bank 1 F x)+∑ x, hopTerm C U x a := by
  rw [sub_eq_add_neg,copies_add,form_add]; congr 1
  · simpa only [Complex.ofReal_one,one_smul] using banker (n:=n) F 1
  rw [singleHop,neg_add,copies_add,form_add,onSpin,onSpin] -- occurs back also
  unfold shift
  rw [ride_ad,ride_mul,ride_mul]
  have hh (e : Equiv.Perm (Site n)) (B : Site n → Bundle) : form (copies F (-rides e B))=
      ∑ x, -(linkB x (e x) (copies F (B x))) := by
    rw [copies_neg]; rw [show form (- copies F (rides e B))= -(form (copies F (rides e B))) by simp [form]]
    rw [groups]; simp only [sum_neg_distrib]
  rw [hh,hh]
  simp only [Equiv.refl_apply,Equiv.refl_trans,touch_star]
  nth_rw 2 [← Equiv.sum_comp (Lat.forward a)]
  unfold hopTerm spans down up
  simp_rw [Equiv.symm_apply_apply,hop,sub_eq_add_neg,sum_add_distrib]
lemma bare_basis (C : Lat.Cut n F) (U : Grid n) :
    form (C.ferm U)=(∑ x,bank (C.m+4) F x)+∑ x,∑ a : Axis, hopTerm C U x a := by
  have hh {i : Type} (s : Finset i) (f : i → Sheet n) : form (copies F (∑ a ∈ s, f a)) = ∑ a ∈ s, form (copies F (f a)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [copies,form,Matrix.blockDiagonal_apply,ite_smul]
    | @insert i s hi ih => rw [sum_insert hi,sum_insert hi,copies_add,form_add,ih]
  rw [Lat.Cut.ferm,bareD,copies_add,form_add,hh,banker]
  simp_rw [bridge_basis,sum_add_distrib]
  simp only [sum_const, card_univ,Fintype.card_fin, Axis]
  rw [← add_assoc]; congr 1
  · rw [← sum_nsmul, ← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_
    rw [bank,bank,bank,Complex.ofReal_add,add_smul,linkB_add, Complex.ofReal_ofNat,Complex.ofReal_one,
      one_smul,linkB_smul i i (1:Short F) (4:ℂ)]; norm_cast
  exact sum_comm

lemma glows (F : ℕ) (a : Axis) (Y : Spike) (T : Mat) :
    glow a F * copies F (wave Y * touch T)*glow a F=copies F (wave (gamma a*Y*gamma a)*touch T) := by
  unfold glow lamp; rw [← copies_mul,← copies_mul,← mul_assoc,wave_mul,
    mul_assoc, (interlace ..).eq,← mul_assoc, wave_mul]
lemma link_star (Y : Spike) (T : Mat) : star (wave Y*touch T)=wave (star Y)*touch (star T) := by rw [star_mul,wave_star,touch_star,(interlace ..).eq]
lemma tang_span (R : Cells.Cut n) {a : Axis} (h : a≠R.pos) (T : Mat) (x y : Site n) :
    theta R (spans F a T x y) = spans F a T (R.reflect x) (R.reflect y) := by
  unfold spans down up
  rw [map_sub,map_neg,theta_B,theta_B,← copies_star,← copies_star, link_star,link_star, star_star,lo_star,hi_star,
    glows,glows,tangent _ _ h.symm, tangent' _ _ h.symm]; abel
lemma chord_span (R : Cells.Cut n) (T : Mat) (x y : Site n) :
    theta R (spans F R.pos T x y) = spans F R.pos (star T) (R.reflect y) (R.reflect x) := by
  unfold spans down up
  rw [map_sub,map_neg,theta_B,theta_B,← copies_star,← copies_star, link_star,link_star,lo_star,hi_star,glows,glows,
    gamma_lo, gamma_hi,neg_mul, odd_lo,neg_neg, even_hi]
end YM.QCD.RP
