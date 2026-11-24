import YM.TorusPCAC.Ward.SD

/-!
# The bias kernel calculation (left derivative throughout)

**All actual density inputs**, not on vacuum, no locality or
invertibility assumptions on the stencil. Since push uses real unity kernel
in this regulator set b fixed to 1. Full complex coefficient EQ even for
singular f (when not inverting in the readout).
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Ward
open QCD QCD.Grass QCD.Kit Finset Function
open scoped Matrix Topology BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Both slots column notation. `s=false` is the ψ slot. -/
def bin {X : Type*} (s : Bool) (i : X) : Pairs X := if s then .inr i else .inl i
abbrev letter (s : Bool) (i : A) : Grass.Dirac A:=atom (bin s i)
abbrev D (s : Bool) (i : A) := vary (bin s i)

abbrev st (s : Bool) (M : Matrix B A ℂ) := if s then Mᴴᵀ else M

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
lemma bin_inj (s : Bool) : Injective (bin (X:=A) s) := by cases s <;> simp [Injective,bin]

omit [DecidableEq B] [DecidableEq A] in
lemma varying (M N : Matrix B A ℂ) (s : Bool) (j : A) (x : Grass.Dirac B) :
    D s j (adapter M N x) = ∑ i, (if s then N i j else M i j) • adapter M N (D s i x) := by
  unfold D adapter
  rw [vary_maps (I:=Pairs B)]; cases s <;> simp [Fintype.sum_sum_type,bin,Pairs]

variable (Q : Matrix B A ℂ)

def noise : Grass.Dirac (A ⊕ B) := gauss (joinD 1 Q 0)

def avgAtom (s : Bool) (i : B) : Grass.Dirac A := ∑ j, st s Q i j • letter s j

lemma noisy : noise Q=skin Q (far A B (gauss 1)):=by rw [noise,generate]; simp [gauss,Grass.form]

section
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
lemma cool_eq (s : Bool) (p : B) : cool A (bin s p)=bin s (Sum.inr p):=by cases s <;> rfl
lemma warm_eq (s : Bool) (p : A) : warm B (bin s p)=bin s (Sum.inl p):=by cases s <;> rfl

end
lemma shift_keep (s : Bool) (p : B) (x : Grass.Dirac (A ⊕ B)) :
    D s (Sum.inr p) (skin Q x)=skin Q (D s (Sum.inr p) x) := by
  unfold skin; rw [varying]; cases s <;> simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul]

lemma shift_tax (s : Bool) (p : A) (x : Grass.Dirac (A ⊕ B)) :
    D s (Sum.inl p) (skin Q x)=skin Q (D s (Sum.inl p) x) - ∑ u : B,
      st s Q u p • skin Q (D s (Sum.inr u) x) := by
  unfold skin; rw [varying]; cases s <;> simp [Fintype.sum_sum_type,Matrix.one_apply, ite_smul,st,sum_neg_distrib,sub_eq_add_neg]

lemma shift_far (s : Bool) (p : B) : skin Q (far A B (letter s p)) =
    letter s (Sum.inr p) - near A B (avgAtom Q s p) := by
  unfold skin far avgAtom near; cases s
  · change adapter _ _ (pass _ (psi p))= psi (Sum.inr p)-pass Sum.inl (∑ a, Q p a • psi a)
    rw [pass_psi,adapt_psi]
    simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul,sum_neg_distrib]; abel
  change adapter _ _ (pass _ (bar p))=bar (Sum.inr p)-pass Sum.inl (∑ a, Qᴴ a p • bar a)
  rw [pass_bar,adapt_bar]; simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul,sum_neg_distrib]; abel

lemma hot_noise (s : Bool) (p : A) : D s (Sum.inl p) (noise Q)=-(∑ u : B, st s Q u p • (D s (Sum.inr u) (noise Q))) := by
  simp_rw [noisy,shift_tax,shift_keep]; rw [D,←warm_eq,warm_silent,map_zero,zero_sub]

lemma column_form (i : A) : vary (Sum.inl i) (Grass.form (1 : Matrix A A ℂ))=bar i := by
  rw [show Grass.form (1:Matrix A A ℂ)=∑ j : A, psi j * bar j by simp [Grass.form, Matrix.one_apply,ite_smul],map_sum];
  rw [sum_eq_single i]
  · rw [vary_mul,vary_self,vary_off (X:=Pairs A) (Sum.inl i) (Sum.inr i) (by simp),one_mul,mul_zero,add_zero]
  · intro k _ hk; rw [vary_mul,vary_off _ (Sum.inl k) (by simp [Ne.symm hk]), vary_off (X:=Pairs A) (Sum.inl i) (Sum.inr k) (by simp),zero_mul,mul_zero,add_zero]
  simp

lemma row_form (i : A) : vary (Sum.inr i) (Grass.form (1 : Matrix A A ℂ))=-psi i := by rw [Grass.form_row]; simp [Matrix.one_apply,ite_smul]

/-- With s referring to *letter*, let `sgn` be the sign of derivative of the Gaussian
in the **opposite slot**. Thus e.g. to create ψ (s=false) we use `∂bar`, sign -.
-/
def sign (s : Bool) : ℂ := if s then 1 else -1

lemma derivative_letter (s : Bool) (i : A) : D (!s) i (gauss (1 : Matrix A A ℂ))= sign s • (letter s i * gauss 1) := by
  unfold D gauss; rw [varies_exp _ _ (form_plus _)];
  change gauss 1 * vary _ _ = _
  rw [← ((gauss_plus (1:Matrix A A ℂ)).central _).eq]
  cases s
  · change vary (Sum.inr i) _ * _ = (-1:ℂ) • (psi i*_)
    rw [row_form]; simp [gauss]
  change vary (Sum.inl i) _ * _ = (1:ℂ) • (bar i*gauss 1)
  rw [column_form,one_smul]

lemma cool_noise (s : Bool) (p : B) : D (!s) (Sum.inr p) (noise Q)= sign s •
     ((letter s (Sum.inr p) - near A B (avgAtom Q s p))*noise Q) := by
  simp_rw [noisy,shift_keep]; rw [D,←cool_eq,cool_survives]; rw [derivative_letter]; simp only [map_smul,map_mul,shift_far]

end YM.TorusPCAC.Ward
