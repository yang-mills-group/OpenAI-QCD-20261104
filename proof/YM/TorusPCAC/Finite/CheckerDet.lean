import YM.TorusPCAC.Finite.Checker
import YM.QCD.Lattice.Stability

/-!
# Checker saturation: the decoupled determinant

Multiply all rows from sites in `S` by `t>0` and add onsite mass `t⁻¹`
for those sites (before that scaling). The resulting determinant extends
through t=0, where the corresponding rows are identity rows. Require
exact row rather than just asymptotic eigenvalue upper bounds. At the
checker placement the rest of the sites are pairwise nonadjacent: the
surviving determinant is exactly the product of onsite diagonal entries of
the unsaturated rows. In particular no measure sign estimate is used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Finite.Checker
open QCD QCD.Lat Lattice Wilson MeasureTheory Function Finset Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius Matrix Kronecker
variable {n : Side} {N : ℕ}

namespace Width
variable (w : Width n) (B : Torus n N) (S : Finset (Site n))

def test (t : ℝ) (i : Site n) := if i∈S then t⁻¹ else 0

def diagonal (n : Side) (N : ℕ) (s : Site n → ℂ) : Matrix (Modes n N) (Modes n N) ℂ := Matrix.diagonal (fun i => s i.1.1)

def shift (t : ℝ) (U : Grid n) : Matrix (Modes n N) (Modes n N) ℂ :=
  diagonal n N (fun x => if x∈S then ↑t else 1)*B.fermion U +
      diagonal n N (fun x => if x∈S then 1 else 0)

lemma posShift (U : Grid n) {t : ℝ} (ht : t ≠ 0) :
    shift B S t U =
      diagonal n N (fun x=> if x∈S then ↑t else 1)*(B.fermion U+Marker.matrix n N (test S t)) := by
  rw [mul_add,shift]; congr 1; unfold Marker.matrix test diagonal; rw [Matrix.diagonal_mul_diagonal]; congr; funext i
  by_cases hi:i.1.1∈S <;> simp [hi,ht]

lemma sitewise (s : Site n → Flavor N → ℂ) : ∏ i : Modes n N, s i.1.1 i.2 =
    ∏ i : Site n, ∏ j : Flavor N, (s i j)^12 := by
  rw [Fintype.prod_prod_type]; dsimp only
  rw [Fintype.prod_prod_type]; apply prod_congr rfl; intro i _
  change (∏ _ : Fiber, (∏ j : Flavor N, s i j))=_
  rw [prod_const,card_univ, ← prod_pow]
  simp [Fiber,Pinor,Hue]

abbrev bill (N : ℕ) (S : Finset (Site n)) := 12*N*S.card

lemma filter_prod (s t : Flavor N → ℂ) : ∏ i : Modes n N, (if i.1.1∈S then s i.2 else t i.2)=
    (∏ i, (s i)^12)^S.card * (∏ i, (t i)^12)^Sᶜ.card := by
  let f (i : Site n) (j : Flavor N) := if i∈S then s j else t j
  change (∏ i:Modes n N,f i.1.1 i.2)=_; rw [sitewise f]
  rw [show (fun i => ∏ j,(f i j)^12)=(fun i => if i∈S then ∏ j,(s j)^12 else ∏ j,(t j)^12) by
    funext i; by_cases hv : i∈S <;> simp [f,hv],prod_ite]
  rw [show univ.filter (fun i=>i∈ S)=S by ext; simp, show univ.filter (fun i=>i∉ S)=Sᶜ by ext; simp,prod_const,prod_const]

lemma detShift (t : ℝ) (U : Grid n) (ht : t ≠ 0) :
    (shift B S t U).det=(t:ℂ)^(bill N S)*(B.fermion U+Marker.matrix n N (test S t)).det := by
  rw [posShift B S U ht, Matrix.det_mul]; congr 1
  rw [diagonal,Matrix.det_diagonal]; rw [filter_prod S (N:=N) (fun _=>t) (fun _=>1)]
  simp only [prod_const,card_univ,Flavor,Fintype.card_fin,one_pow,mul_one]; rw [← pow_mul, ← pow_mul,← mul_assoc (12:ℕ)]

lemma hop_loss (t : Site n) (U : Grid n) (a : Axis) (x y : Row n)
    (hx : x.1∉w.occupied) (hy : y.1∉w.occupied) :
    singleHop t U a x y=0 := by
  rw [Lat.hop_read, if_neg ?_,if_neg ?_,zero_add]
  · intro he; apply hx
    rw [sub_eq_iff_eq_add] at he
    rw [he]; exact (w.mem_hop a _).mpr (mem_compl.mpr hy)
  intro he; apply hy
  rw [← he]; exact (w.mem_hop a _).mpr (mem_compl.mpr hx)

lemma checkerBlock (U : Grid n) (x y : Modes n N)
    (hx:x.1.1∉w.occupied)(hy:y.1.1∉w.occupied) :
    B.fermion U x y=if x=y then ((4+B.mass x.2 : ℝ):ℂ) else (0:ℂ) := by
  rw [B.block_read]; unfold Lat.bareD; split_ifs with h h' h''
  · subst y; simp_rw [Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply, w.hop_loss _ U _ x.1 x.1 hx hx, Matrix.one_apply_eq, sub_zero]; simp [Axis, add_comm]
  · have he : x.1≠y.1 := by intro he; exact h' (Prod.ext he h)
    simp_rw [Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply, w.hop_loss _ U _ x.1 y.1 hx hy]; simp [he]
  · subst y; contradiction
  rfl

private lemma triangular {A : Type*}[Fintype A][DecidableEq A](P : A → Prop)[DecidablePred P]
    (M : Matrix A A ℂ) (d : A→ℂ)
    (h : ∀ i j, P i ∨ ¬ P j → M i j=if i=j then d i else 0) :
    M.det=∏ i,d i := by
  let e := Equiv.sumCompl P; let I:=Subtype P; let J:=Subtype fun x:A=>¬P x
  let f:=Matrix.diagonal fun i:I=>d i.val
  let g:=Matrix.diagonal fun j:J=>d j.val
  rw [← Equiv.prod_comp e d,← Matrix.det_submatrix_equiv_self e]
  have he : M.submatrix e e=Matrix.fromBlocks f 0 (M.submatrix (fun j:J=>j.val) (fun i:I=>i.val)) g := by
    ext (i|i) (j|j)
    · change M i.val j.val = _; rw [h i.val j.val (Or.inl i.property)]; by_cases hx : i=j <;> simp [hx,f]
      exact fun h=> False.elim (hx (Subtype.ext h))
    · change M i.val j.val = _; rw [h i.val j.val (Or.inl i.property), if_neg (show i.val ≠ j.val from fun he=> j.property (he ▸ i.property))]; rfl
    · rfl
    change M i.val j.val = _; rw [h i.val j.val (Or.inr j.property)]; by_cases hx : i=j <;> simp [hx,g]
    exact fun h=> False.elim (hx (Subtype.ext h))
  rw [he,Matrix.det_fromBlocks_zero₁₂]; simp only [f,g, Matrix.det_diagonal,Fintype.prod_sum_type]; rfl

lemma zeroShift (U : Grid n) (x y : Modes n N) :
    shift B S 0 U x y=if x.1.1∈S then (1:Matrix _ _ ℂ) x y else B.fermion U x y := by
  unfold shift diagonal; rw [Matrix.add_apply,Matrix.diagonal_mul]; by_cases h:x=y
  · subst y; by_cases hx:x.1.1∈S <;> simp [hx]
  by_cases hx:x.1.1∈S <;> simp [hx,h]

lemma all (U : Grid n) : (shift B univ 0 U).det=1 := by
  rw [show shift B univ 0 U=1 by ext i j; simp [zeroShift], Matrix.det_one]

/-- Onsite number **per unsaturated site**, not a choice of common mass. -/
def cost := ∏ i : Flavor N, ((4:ℝ)+B.mass i)^12

lemma short (U : Grid n) :
    (shift B w.occupied 0 U).det=(cost B : ℂ)^(w.occupiedᶜ.card) := by
  let d (x : Modes n N):ℂ := if x.1.1∈w.occupied then 1 else ↑(4+B.mass x.2)
  have he := @triangular (Modes n N) _ _ (fun x=> x.1.1∈w.occupied) _ (shift B w.occupied 0 U) d
  specialize he (by
    intro i j hp; unfold d; rw [zeroShift]; by_cases h:i.1.1∈w.occupied; · simp only [h, ↓reduceIte, Matrix.one_apply]
    have hh : j.1.1∉w.occupied := hp.resolve_left h
    simp only [h,↓reduceIte,checkerBlock w B U i j h hh])
  unfold d at he
  rw [he, filter_prod (N:=N) _ (fun _=>1) (fun i=> ↑(4+B.mass i))]
  simp only [one_pow, prod_const_one,one_mul,cost]; push_cast; rfl
end Width
end YM.TorusPCAC.Finite.Checker
