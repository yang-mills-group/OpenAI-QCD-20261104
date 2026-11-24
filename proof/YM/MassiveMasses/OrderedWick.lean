import YM.MassiveMasses.FreePair

set_option autoImplicit false
noncomputable section

namespace YM.MassiveMasses.FreePair
open Lattice QCD QCD.Lat Massive Massive.UV
open scoped BigOperators Kronecker

/-- Four actual occurrences, in the order bar(a), psi(b), bar(b), psi(a)
of the two exterior products appearing in UV.bilinear. -/
def orderedFour (d : ℕ) (a b : Fin 6) (x : Points 2) (i j k l : Fiber) : ℂ :=
  Free.pf (Free.pair (u := fun _ => d) x) 4
   [⟨0,.inr ((0,i),a)⟩, ⟨0,.inl ((0,j),b)⟩, ⟨1,.inr ((0,k),b)⟩, ⟨1,.inl ((0,l),a)⟩]

theorem fourLetters {T : Type} (f : T → T → ℂ) (p q r s : T) :
    Free.pf f 4 [p,q,r,s] = f p q*f r s - f p r*f q s + f p s*f q r := by
  simp [Free.pf,Fin.sum_univ_succ,List.eraseIdx]
  ring

private lemma zeroSteps (d : ℕ) : Free.steps (0 : Multi d) = [] := by
  simp [Free.steps,UV.power]
  intro j
  rfl

private lemma ordinaryLeg {d : ℕ} (a : Fin 6) (i j : Fiber) {x y : E4} (h : x ≠ y) :
    Free.leg (d:=d) (e:=d) ((0,i),a) ((0,j),a) x y = prop (x-y) i j := by
  rw [prop_entry _ (sub_ne_zero.mpr h) i.1 j.1 i.2 j.2]
  simp [Free.leg,zeroSteps,Free.derivatives]

theorem orderedFour_value (d : ℕ) (a b : Fin 6) {x : Points 2} (h : x 0 ≠ x 1)
    (i j k l : Fiber) :
    orderedFour d a b x i j k l = -(prop (x 0-x 1) j k * prop (x 1-x 0) l i) := by
  rw [orderedFour,fourLetters]
  simp [Free.pair, ordinaryLeg a l i h.symm, ordinaryLeg b j k h]
  ring

def expand (M : Spike) (f : Fiber → Fiber → ℂ) : ℂ :=
  ∑ i, ∑ j, wave M i j * f i j

/-- This is precisely the single color sum used by UV.bilinear. -/
theorem expandBilinear (M : Spike) (f : Fiber → Fiber → ℂ) :
    expand M f = ∑ s : Pinor, ∑ t : Pinor, ∑ c : Hue, M s t * f (s,c) (t,c) := by
  unfold expand
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  have split (c : Hue) : (∑ j : Fiber, wave M (s,c) j * f (s,c) j) =
      ∑ t : Pinor, ∑ e : Hue, wave M (s,c) (t,e) * f (s,c) (t,e) := by
    rw [Fintype.sum_prod_type]
  simp only [split]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro c _
  simp [wave,Matrix.kroneckerMap_apply,Matrix.one_apply,mul_ite,ite_mul]

theorem expandFour (d : ℕ) (a b : Fin 6) {x : Points 2} (h : x 0 ≠ x 1) :
    expand g5 (fun i j => expand g5 (orderedFour d a b x i j)) = wickTrace (x 0-x 1) := by
  have rev : -(x 0-x 1) = x 1-x 0 := neg_sub ..
  simp only [expand,orderedFour_value d a b h,wickTrace,rev,mul_assoc,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Full color and pinor sums in the literal coefficient and barred/unbarred
ordering of the target's two pseudoscalar bilinears. -/
theorem orderedBilinearSum (d : ℕ) (a b : Fin 6) {x : Points 2} (h : x 0 ≠ x 1) :
    (∑ i : Pinor, ∑ j : Pinor, ∑ r : Hue, g5 i j *
      (∑ k : Pinor, ∑ l : Pinor, ∑ s : Hue, g5 k l *
         orderedFour d a b x (i,r) (j,r) (k,s) (l,s))) = wickTrace (x 0-x 1) := by
  simpa only [expandBilinear] using expandFour d a b h

end YM.MassiveMasses.FreePair
#print axioms YM.MassiveMasses.FreePair.orderedFour_value
#print axioms YM.MassiveMasses.FreePair.orderedBilinearSum
