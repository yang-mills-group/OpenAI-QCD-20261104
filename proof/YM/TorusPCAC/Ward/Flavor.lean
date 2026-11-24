import YM.TorusPCAC.Ward.History
import YM.TorusPCAC.Spec.FieldsReg

/-!
# Exact flavor elimination even in the passenger step

Use U(1)^N action on the *actual* sea, no Link-flat hypothesis. It
comes from the same Q. Hence the degree two mixed planes used below are
eliminated exactly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Ward
open QCD QCD.Grass QCD.Lat QCD.Kit Lattice Wilson Finite Finset MeasureTheory Function RG
open scoped Matrix Topology BigOperators Kronecker Matrix.Norms.Frobenius
variable {A : Type*} [Fintype A]

abbrev zeroR := coef (∅: Finset A)
lemma keeps_zero (X : Matrix A A ℂ) (v : Alg A) : zeroR (changeVars X v)=zeroR v:=by
  rw [← write v]; simp only [map_sum,map_smul]; refine sum_congr rfl (fun i _ => ?_)
  by_cases h : i=∅
  · subst i; rw [mono_empty,map_one]
  rw [show zeroR (changeVars X (mono i))=0 from spectrum (Grass.exterior_layer _ (homogeneous i)) _
    (fun e=> h (by rw [← Finset.card_eq_zero]; exact e.symm)),show zeroR (mono i)=0 from read_other _ _ (Ne.symm h)]

variable {c f n : Side} {N : ℕ}
abbrev Grade (N : ℕ) := Flavor N → Circle

def tag (n : Side) (u : Grade N) : MatS n N := Matrix.diagonal (fun i => (u i.2:ℂ))
def acts (u : Grade N) (n : Side) := disguise (tag n u)
lemma acts_stencil (u : Jet.FlavorGroup) : acts u n=Stencil.rotateFlavor n u:=by
  unfold acts Stencil.rotateFlavor disguise Stencil.flavorMatrix tag
  rw [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,Matrix.diagonal_transpose]

lemma tag_star (u : Grade N) : star (tag n u) = tag n u⁻¹ := by
  rw [tag, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]; unfold tag; congr 1; funext x; exact (Circle.coe_inv_eq_conj _).symm
lemma tag_unit (u : Grade N) : tag n u ∈ unitary _:=by
  constructor
  · rw [tag_star]; ext i j; by_cases h : i=j <;> simp [tag,h,Matrix.one_apply]
  rw [tag_star]; ext i j; by_cases h : i=j <;> simp [tag,h,Matrix.one_apply]

lemma tag_formula (u : Grade N) (B : Torus n N) (U : Grid n) : acts u n (B.weight U)=B.weight U:=by
  have hh : tag n u * B.fermion U = B.fermion U * tag n u := by
    ext i j; simp only [tag, Matrix.mul_diagonal,Matrix.diagonal_mul,B.block_read]; split
    next he => rw [he,mul_comm]
    simp
  rw [B.weight_complex,map_smul]; congr 1
  have he := disguised (tag_unit (n:=n) u) (B.fermion U); rw [hh,mul_assoc,(tag_unit u).2,mul_one] at he; exact he

lemma tag_step (u : Grade N) (M : StepData c f) (U : Grid f) : meanSpin M U * tag f u= tag c u * meanSpin M U:=by
  ext i j; simp only [tag, Matrix.mul_diagonal,Matrix.diagonal_mul,meanSpin,Matrix.blockDiagonal_apply]; split
  next h=> rw [h,mul_comm]
  simp

lemma high_acts (u : Grade N) (F : Density f N) (M : StepData c f) (U : Grid f) : acts u c (TorusPCAC.high M F U)=TorusPCAC.high M (fun V=>acts u f (F V)) U:=by
  have he := compat (tag_unit (n:=f) u) (tag_unit (n:=c) u) 1 (meanSpin M U) (F U)
  rw [← tag_step u M U,Matrix.mul_assoc, (tag_unit u).2,Matrix.mul_one] at he; exact he

lemma temp_acts {u : Grade N} (v : Fields n N) (w : ℂ) : temp w (acts u n v)=acts u n (temp w v):=by unfold temp acts disguise; simp [adapt_together]

lemma high_stable (u : Grade N) {F : Density f N} (h : (fun U=>acts u f (F U))=F) (hc : Continuous F) (M : StepData c f) (he : M.patch.Branches M.kernel su) (V) (b w : ℝ) : acts u c (block M b w F V)=block M b w F V:=by
  unfold block
  change acts u c (temp (↑w) _)=_
  rw [←temp_acts]
  have hg : (fun U=> acts u c (TorusPCAC.high M F U))=TorusPCAC.high M F:=funext fun U=>by rw [high_acts,h]
  have hi := Pass.evaluate M (N:=N) b he (acts u c).toLinearMap (TorusPCAC.high M F)
    ((high_cont M _ hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..))
  simp only [AlgHom.toLinearMap_apply,hg] at hi; rw [← congr_fun hi V]; rfl

lemma holds (u : Grade N) (H : History N) {q m} (h : m≤H.depth q) : (fun U=> acts u _ (H.actual q m U))=H.actual q m := by
  induction h using Nat.decreasingInduction with
  | self => simp_rw [H.actual_at, tag_formula]
  | of_succ i hi ih => rw [H.actual_next q hi]; exact funext fun V=> high_stable u ih (H.actual_cont q hi) _ (H.branches i) ..

/-- Suffices even to use `±1` to justify these off-flavor zeros. -/
def flipFlav (i : Flavor N) : Grade N := fun j=> if i=j then -1 else 1
lemma flipInv (i : Flavor N) : (flipFlav i)⁻¹=flipFlav i := by ext1 j; by_cases h : i=j <;> simp [flipFlav,h]

lemma flipD (s : Bool) (x : Fields n N) (i : Flavor N) (p : Modes n N) : D s p (acts (flipFlav i) n x)= (if i=p.2 then -1 else (1:ℂ)) • acts (flipFlav i) n (D s p x) := by
  unfold acts disguise; rw [varying,tag_star,flipInv]
  simp only [tag, Matrix.diagonal_transpose,ite_self]
  rw [sum_eq_single p]
  · rw [Matrix.diagonal_apply_eq]; cases em (i=p.2) <;> simp [flipFlav, *]
  · intro k _ hk; simp [hk]
  simp

lemma segregated (s t : Bool) (i j : Modes n N) (x : Fields n N) (he : i.2 ≠ j.2) (hp : ∀ u : Grade N, acts u n x=x) : zeroR (D s i (D t j x))=0 :=by
  refine neg_eq_self.mp ?_
  nth_rw 2 [← hp (flipFlav i.2)]
  rw [flipD t x,if_neg he,one_smul,flipD,if_pos rfl,neg_smul, one_smul,map_neg]; rw [show zeroR (acts (flipFlav i.2) n _)=_ from keeps_zero ..]

/-- Endpoints i,j always address this pair of different flavors. Everything
integrated in `car` carries no external Grassmann variables outside `Modes`.
-/
def Belongs (p : Pair N) (F : Pass n N) := ∀ i j : Modes n N,
     (p.l ≠ i.2 ∨ p.r ≠ j.2) → F.car i j=0
lemma belongs (p : Pair N) (H : History N) (q M m : ℕ) (h : m≤M) (X : Density (H.lattice M q) N) (hx : Continuous X) : Belongs p (History.haul H q M p X hx m) := by
  induction h using Nat.decreasingInduction with
  | self => exact fun i j _ => (History.boundary ..).2 i j
  | of_succ k he ih =>
    rw [History.haul_next H p _ _ he]
    let S := H.step k q
    let A := History.haul H q M p X hx (k+1)
    intro i j hg
    have hv : ¬(i.2=p.l ∧ j.2=p.r):=fun h=> hg.elim (· h.1.symm) (· h.2.symm)
    have hw : p.symbol (H.lattice k q) i j=0:= by simp [Pair.symbol,Pair.flavor,hv]
    have hA : Pass.massMixD A S i j=0:= by
      ext1 U; unfold Pass.massMixD massMix; refine sum_eq_zero (fun y _=> sum_eq_zero (fun z _=> ?_))
      by_cases ht : i.2=y.2 <;> by_cases hu : j.2=z.2
      · dsimp only [A]; rw [ih y z (by rwa [← ht,← hu]),Pi.zero_apply,smul_zero,smul_zero]
      all_goals simp [Matrix.conjTranspose_apply,meanSpin,Matrix.blockDiagonal_apply, *]
    dsimp only [A,S] at hA; dsimp only [Pass.onward]; rw [hw, hA,zero_smul, zero_add]
    have h0 : block S (H.beta q (k+1)) (H.w q k) (0: Density _ N)=0:= by
      ext1 U; simp [block,TorusPCAC.high,sheath,StepData.push]
    dsimp only [S] at h0; rw [h0,smul_zero]
end YM.TorusPCAC.Ward
