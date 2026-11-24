import YM.Massive.RG.Motion
import YM.Massive.Finite.Strict

/-!
# Normalization on one unequal-mass regulated history of any depth

The β history in this theorem is given; the stiffness condition and calibrated
infrared targets are NOT proved just by this normalization. Makes no proximity
to the determinant of a degenerate trajectory assumption. It will apply e.g. if
there's a parameter selector choosing negative bare masses near 0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Grass QCD.Lat MeasureTheory Function Filter RG Lattice Wilson
open scoped BigOperators Topology Matrix ComplexOrder

variable {n : Side} {F : ℕ}
lemma Regulator.invariant {R : Regulator n F} : Lat.Invariant R.density := by -- params
    rw [R.compareDensity]; apply invariant_mul
    · intro k; ext1 i
      change slots _ _ _ = _; rw [Regulator.density_apply (Regulator.common _), map_smul,bare_gauge]
      have h := invariant_weight k R.zeroCut i
      rw [Regulator.density_apply (Regulator.common _)]; exact congr_arg ((bare R.β i:ℂ) • ·) h
    exact Onsite.patch_invariant _ _

namespace Scheme
open Transfer
variable {m N F : ℕ} (S : Scheme) (R : Side)
variable (β w : ℕ → ℝ)

def send (m : ℕ) : Insertion (S.side R (m+1)) F →ₗ[ℂ] Insertion (S.side R m) F :=
  blockMap (S.step m) S.choices (S.sides_next R m) (β (m+1)) (w m) (S.admissible m)

/-- Compose the full step operators. Keep values only for stops `m≤N`. -/
def toStop (S : Scheme) (R : Side) (β w : ℕ → ℝ) {F : ℕ} (N m : ℕ) :
    Insertion (S.side R N) F →ₗ[ℂ] Insertion (S.side R m) F :=
    if h : m=N then h ▸ LinearMap.id else if _h' : m<N then
      (S.send R β w m).comp (S.toStop R β w N (m+1)) else 0
termination_by N-m

lemma entrance : S.toStop R β w N N (F:=F) = LinearMap.id := by rw [toStop]; simp

lemma next (h : m<N) (x : Insertion (S.side R N) F) :
   S.toStop R β w N m x = S.send R β w m (S.toStop R β w N (m+1) x) := by rw [toStop]; simp [h.ne,h]

variable {u : Flavor F → ℝ}

def wilson (u : Flavor F → ℝ) (N : ℕ) : Regulator (S.side R N) F := ⟨β N, 0, u⟩

def run (u : Flavor F → ℝ) (N : ℕ) : Run S N R F where
  β := β
  w := w
  u := u
  density := fun m => S.toStop R β w N m (S.wilson R β u N).density

lemma carried (x : Insertion (S.side R N) F) (u : Flavor F → ℝ) :
    (S.run R β w u N).Carried (fun i => ⇑(S.toStop R β w N i x)) 0 := by
  constructor
  · exact fun _ _ => Continuous.integrable_of_hasCompactSupport (ContinuousMap.continuous _)
        (HasCompactSupport.of_compactSpace _)
  · intro i _ _; exact soften_pay (S.step i) _ (ContinuousMap.continuous _)
  intro i _ hi; rw [next S R β w hi x]; rfl

lemma atStop {f : ∀ i, Density (S.side R i) F}
    (u : Flavor F → ℝ) (Y : (S.run R β w u N).Carried f 0) (x : Insertion (S.side R N) F)
    (he : f N=x) (m : ℕ) (hm : m ≤ N) : f m=S.toStop R β w N m x := by
    induction hm using Nat.decreasingInduction with
    | self => simpa only [entrance, LinearMap.id_apply] using he
    | of_succ k hk ih => rw [Y.eqn (Nat.zero_le _) hk, ih, next S R β w hk x]; rfl

lemma transport_gauge (x : Insertion (S.side R N) F) (hx : Lat.Invariant x) (hm : m ≤ N) :
    Lat.Invariant (S.toStop R β w N m x) := by
    induction hm using Nat.decreasingInduction with
    | self => rw [entrance]; exact hx
    | of_succ k hk ih => rw [next S R β w hk x]; exact invariant _ _ (S.step k) S.choices _ (S.admissible k) _ ih

lemma parity (x : Insertion (S.side R N) F) (p : Bool) (hx : ∀ i, Grass.Hom p (x i)) (hm : m ≤ N) :
    ∀ i, Grass.Hom p (S.toStop R β w N m x i) := by
    induction hm using Nat.decreasingInduction with
    | self => rw [entrance]; exact hx
    | of_succ k hk ih => rw [next S R β w hk x]; exact Transfer.homogeneous _ _ (S.step k) _ _ (S.admissible k) _ p ih

def multiplier (m N F : ℕ) := ∏ i ∈ Finset.Ico m N, growth (S.side R i) F (w i)

lemma nextMultiplier (h : m<N) : S.multiplier R w m N F = growth (S.side R m) F (w m) * S.multiplier R w (m+1) N F := by
    unfold multiplier; rw [← Finset.insert_Ico_add_one_left_eq_Ico h,Finset.prod_insert (by simp)] -- check

lemma conservation {A : Run S N R F} (Z : ∀ i, Density (S.side R i) F)
    (terminal : ℕ) (Y : A.Carried Z terminal) (hm : m ≤ N) (ht : terminal ≤ m) :
    joint (Z m) = S.multiplier R A.w m N F * joint (Z N) := by
    induction hm using Nat.decreasingInduction with
    | self => simp [multiplier]
    | of_succ k hk ih => rw [Y.eqn ht hk,Run.block,conserves (P:=S.step k) _ _ _ _ (S.admissible k) _ (Y.atStep ht hk), nextMultiplier S R A.w hk, ih (by omega),mul_assoc]

variable (hβ : ∀ m ≤ N, 0 < β m) (hw : ∀ m < N, 0 < w m)
include hw
lemma positive (_hm : m ≤ N) (F : ℕ) : 0 < S.multiplier R w m N F := by
    apply Finset.prod_pos; intro i hi; unfold growth; apply pow_pos; exact Complex.zero_lt_real.mpr (hw i (Finset.mem_Ico.mp hi).2)

include hβ

lemma strict (hR : Even R.val) (hr : 4 ≤ R.val) (hu : ∀ i, u i + 4 ≠ 0) : (S.run R β w u N).Actual := by
    let U := S.wilson R β u N
    let X := S.run R β w u N
    have H : X.Carried X.density 0 := S.carried R β w U.density _
    have h (i) : X.density i=S.toStop R β w N i U.density := rfl
    have he : X.density N = U.density := by rw [h N,entrance]; rfl
    change X.Actual; refine ⟨he,H,fun {i} hi=> hβ i hi,fun {i} hi=> hw i hi,fun {i} hi x=>?_,fun {i} hi x k=> ?_,fun {i} hi=> ?_⟩
    · refine S.parity R β w U.density false (fun x=>?_) hi x
      change Grass.Plus _; rw [Regulator.density_apply]; exact Grass.Hom.smul (p:=false) (gauss_plus _) _
    · rw [h i]; exact DFunLike.congr_fun (S.transport_gauge R β w U.density U.invariant hi k) x
    rw [conservation S R X.density _ H hi (by omega)]; apply mul_pos (positive S R w hw hi _)
    have hn : 4 ≤ (S.side R N).val := hr.trans (Nat.le_mul_of_pos_right R.val (S.ratio N).property)
    have hc : Even (S.side R N).val:= Even.mul_right hR _
    have hb := Checker.nonzero U (hβ N le_rfl).le hc hn hu
    rw [he]; unfold Regulator.Z at hb; change 0 < joint ⇑(U.density*1) at hb; rwa [mul_one] at hb
end Scheme
end YM.Massive
#print axioms YM.Massive.Scheme.strict
