import YM.TorusPCAC.Finite.Weight
import YM.QCD.RP.Floor

/-!
# Unequal masses and positivity

Proof of the (unnormalized!) RP statement used in `work/bend`.
No continuity neighborhood of even flavor degeneracies is required. Use
the reflection in *either* convention (the seam-compatible `reflect`,
or as usual `picture R C` incorporating change of spin seams). Permit also
all the odd test operators. Thanks to the work already done on Wilson RP in
the supplied QCD tree, it suffices to recognize the exact factor induced
by unequal real masses as itself a reflection square. Record also
nonnegativity of the actual total partition on all even sides usable for
these link cuts (independent of what happens to the pointwise gauge
marginal off the even-degeneracy axis).
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Finite
open QCD QCD.Lat Lattice Wilson QCD.RP NormedSpace MeasureTheory Function Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Matrix ComplexOrder

namespace Slab
variable {n : Side} {N : ℕ} (R : Cells.Cut n) (B : Torus n N)

def assign (s : Site n → ℝ) : Matrix (Modes n N) (Modes n N) ℂ :=
  Matrix.diagonal fun i => ↑(s i.1.1 * B.mass i.2)

theorem assign_one : assign B 1 = B.massMatrix := by
  ext ⟨i,l⟩ ⟨j,m⟩
  by_cases h : i=j <;> by_cases hh : l=m <;>
    simp [assign,Torus.massMatrix,Matrix.blockDiagonal_apply,h,hh]

theorem assign_add (s t : Site n → ℝ) : assign B (s+t) = assign B s + assign B t := by
  rw [assign,assign,assign,Matrix.diagonal_add]; simp_rw [Pi.add_apply,add_mul,Complex.ofReal_add]

theorem assign_real (s : Site n → ℝ) : star (assign B s) = assign B s := by
  unfold assign; rw [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp only [Pi.star_apply,Complex.star_def, Complex.conj_ofReal]

def atoms (x : Site n) := ∑ i : Wind N,
  (B.mass i.2:ℂ) • (Grass.psi (place x i)*Grass.bar (place x i))

theorem form_assign (s : Site n → ℝ) : Grass.form (assign B s) = ∑ x : Site n, (s x:ℂ) • atoms B x := by
  unfold Grass.form
  have he (i : Modes n N) : ∑ j : Modes n N, assign B s i j • (Grass.psi j* Grass.bar i)=
      ((s i.1.1 * B.mass i.2 : ℝ):ℂ) • (Grass.psi i* Grass.bar i) := by
    rw [sum_eq_single i]; · simp [assign]
    · intro j _ hj; simp [assign,Ne.symm hj]
    simp
  simp_rw [he]; rw [placed_sum]
  refine sum_congr rfl fun x _ => ?_
  unfold atoms; rw [smul_sum]; apply sum_congr rfl; intro i _
  simp only [Complex.ofReal_mul,smul_smul]; rfl

open scoped Classical in
/-- Membership in the strict plus-side site set. -/
def indicator (x : Site n) : ℝ := if x∈R.sector then 1 else 0

def half : Insertion n N := ContinuousMap.const _ (Grass.gauss (assign B (indicator R)))

theorem sided : Floors R.sector (half R B) := by
  classical
  rw [QCD.RP.sided]
  let g := ∑ x : Sky R, ∑ i : Wind N,
    (B.mass i.2:ℂ) • (Grass.psi (place x i)*Grass.bar (place x i))
  let t := indicator R
  refine ⟨fun _ => exp g,continuous_const,(fun _ _ _ => rfl),fun _ => ?_⟩
  change Grass.gauss _ = _
  rw [Grass.gauss,form_assign, Grass.map_weight]
  congr 1
  have he : Grass.pass (light R) g = ∑ x : Sky R, atoms B x.val := by
    unfold g atoms; simp only [map_sum,map_smul,map_mul,Grass.pass_psi,Grass.pass_bar]; rfl
  rw [he,← sum_subtype (univ.filter fun x => x∈R.sector) (by simp) (atoms B), sum_filter]
  apply sum_congr rfl; intro i _; by_cases h : i ∈ R.sector <;> simp [indicator,h]

theorem commute_assign (s : Site n → ℝ) (k : Lat.Frame n) : Commute (assign B s) (rotates N k) := by
  show assign _ _ * _ = _ * _
  unfold assign; ext ⟨⟨x,i⟩,l⟩ ⟨⟨y,j⟩,m⟩
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : x=y <;> by_cases hh : l=m <;>
    simp [h,hh, Lat.rotates,Lat.copies,Matrix.blockDiagonal_apply, siteRot,rr,mul_comm]

theorem invariant : Invariant (half R B) := by
  intro k; ext1 U; change slots N k (Grass.gauss _) = Grass.gauss _
  rw [Lat.slots, Grass.gauss_map, Matrix.transpose_transpose]; congr 1
  rw [(commute_assign B (indicator R) k).eq,← mul_assoc, (rotates_law N k).1,Matrix.one_mul]

theorem reflects_assign (s : Site n → ℝ) : folds R N * assign B s = assign B (s ∘ R.reflect) * folds R N := by
  ext ⟨⟨x,i⟩,l⟩ ⟨⟨y,j⟩,m⟩
  unfold assign; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; dsimp only [Function.comp_apply]
  unfold folds copies; simp only [Matrix.blockDiagonal_apply]; by_cases h : l=m <;> by_cases hh : R.reflect x=y <;>
    simp [h, hh, Lat.rr, permed, mul_comm]

theorem tape_gauss (T : Tape n) (s : Site n → ℝ) :
    T.tape N (Grass.gauss (assign B s)) = Grass.gauss (assign B s) := by
  rw [Tape.tape,Grass.gauss_map, T.band_trans]
  have he : Commute (assign B s) (T.bands N) := by
    show assign B s * T.bands N = _
    unfold assign Tape.bands; rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]; simp_rw [mul_comm]
  rw [he.eq, ← Matrix.mul_assoc, T.band_sq, Matrix.one_mul]

theorem theta (s : Site n → ℝ) : RP.theta R (Grass.gauss (assign B s)) = Grass.gauss (assign B (s ∘ R.reflect)) := by
  rw [RP.theta, Grass.gauss, Grass.tilt_exp, Grass.tilt_form, assign_real,
    ← Matrix.mul_assoc,reflects_assign,Matrix.mul_assoc,folds_sq,mul_one]; rfl

theorem supported (C : Lat.Cut n N) (U : Grid n) : picture R C (half R B) U =
    Grass.gauss (assign B (indicator R ∘ R.reflect)) := by
  simp_rw [picture,Tape.rolls,reflects]; change (mount R C).tape _ (RP.theta R ((mount R C).tape _ (Grass.gauss _)))=_; rw [tape_gauss,theta,tape_gauss]

theorem unite (h : R.kind=.link) : indicator R ∘ R.reflect + indicator R = (1 : Site n →ℝ) := by
  classical
  funext i; unfold indicator; simp only [Pi.add_apply,comp_apply,Pi.one_apply]; by_cases hi:i∈R.sector
  · simp [R.link_switch h hi,hi]
  simp [hi, (switch R h _).mp hi]

/-- Reflection square. This equality is even as exterior elements, not just
inside an integral. -/
theorem reflect_square (h : R.kind=.link) : B.factor = picture R B.starter (half R B)*half R B := by
  ext1 U
  rw [ContinuousMap.mul_apply,supported]
  change Grass.gauss _ = _ * Grass.gauss _
  rw [← Grass.gauss_add,← assign_add,unite R h,assign_one]

theorem central (C : Lat.Cut n N) (x : Insertion n N) : Commute x (picture R C (half R B)) := by
  show x * _ = _ * x
  ext1 U; rw [ContinuousMap.mul_apply,ContinuousMap.mul_apply,supported]; exact (Grass.gauss_plus _).central _

end Slab

namespace Link
variable {n : Side} {N : ℕ} (R : Cells.Cut n) (h : R.kind=.link)
variable (B : Torus n N)

private theorem common_raw (C : Lat.Cut n N) (x : Insertion n N) (h : R.kind=.link) (hh : 0≤C.β) (hL : 2 ≤ R.half.val)
    (hx : Invariant x) (hf : Floors R.sector x) :
    0 ≤ C.raw (picture R C x*x) := by
  let T := mount R C; have he : T.start=C.t T.a:= rfl
  rw [← T.roll_raw C he,T.roll_mul,picture,Tape.unroll]
  exact raw_positive h (tuned ..) hL hh _ ((RP.sided _).mp (rolling_maps _ hf)) (Tape.roll_invariant _ x hx)

/-- Unequal, real (sign-unrestricted) masses inherit raw RP. Tests on the
supplied whole-sector insertion algebra; a coarse observable needs a
separate support/transport theorem to use this result. -/
theorem raw_positive_mass (x : Insertion n N) (h : R.kind=.link) (hh : 0≤B.beta) (hL : 2≤R.half.val)
    (hx : Invariant x) (hf : Floors R.sector x) :
    0 ≤ Density.moment B.weight (picture R B.starter x * x : Insertion n N) := by
  let C := B.starter; let y := Slab.half R B
  rw [B.moment_eq]
  have he (U) : Grass.Plus (y U) := Grass.gauss_plus _
  have e : Commute y (picture R C x) := by
    show y * _ = _ * y
    ext1 U; exact ((he U).central ((picture R C x) U)).eq.symm
  have ht : B.factor * (picture R C x*x) = picture R C (y*x) * (y*x) := by
    rw [Slab.reflect_square R B h]; change (picture R C y*y)*_= _
    rw [← mul_assoc, mul_assoc (picture R C y) y, e.eq, ← mul_assoc,
      ← (Slab.central R B C (picture R C x)).eq, pic_mul, mul_assoc (picture R C x* picture R C y)]
  rw [ht]
  exact common_raw R _ _ h hh hL (invariant_mul _ _ (Slab.invariant R B) hx) (flooring_mul (Slab.sided R B) hf)
lemma partition_nonneg (h : 4≤n.val) (hb : 0≤B.beta) (he : Even n.val) :
    0 ≤ B.partition := by
  obtain ⟨t,ht⟩:=he; let R : Cells.Cut n:=⟨⟨t,by omega⟩,(show n.val=2*t by omega),.link,timeAxis,0⟩
  have hk := raw_positive_mass R B 1 rfl hb (show 2≤t by omega) Lat.invariant_one RP.flooring_one
  rw [RP.pic_one,mul_one,Density.moment, show (⇑(1 : Insertion n N))=1 from rfl,mul_one,B.volume] at hk
  exact hk.1

lemma normalize_positive (x : Insertion n N) (h : R.kind=.link) (hb : 0≤B.beta) (hL : 2≤R.half.val)
    (hp : 0<B.partition) (hx : Invariant x) (hf : Floors R.sector x) :
    0 ≤ Density.normalize B.weight (picture R B.starter x * x : Insertion n N) := by
  rw [Density.normalize, B.volume,div_eq_mul_inv]
  exact mul_nonneg (raw_positive_mass R B x h hb hL hx hf) (by positivity)

/-- The actual cut with `Matches` can use the `reflect` operation itself. -/
theorem match_plain (x : Insertion n N) (h : Matches B.starter R) :
    picture R B.starter x = RP.reflect R x := by
  let T:=mount R B.starter; have he : T.start=T.stop := h
  have heq (f : Insertion n N) : T.roll f=f := by
    ext1 U; change Grass.adapter (T.bands N) (T.bands N) (f U)=_
    have h1:T.bands N=1:=by unfold Tape.bands Tape.stamp; rw [he]; simp [Matrix.diagonal_one]
    rw [h1,Grass.adapt_one]
  unfold picture; rw [heq,heq]

end Link
end YM.TorusPCAC.Finite
#print axioms YM.TorusPCAC.Finite.Link.normalize_positive
