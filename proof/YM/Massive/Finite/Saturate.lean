import YM.Massive.Finite.Squares

/-! # Onsite saturation observables -/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass QCD.RP Finset Lattice Wilson MeasureTheory Function
open scoped BigOperators Topology Matrix.Norms.Frobenius

namespace Saturate
variable {A : Type*} [Fintype A]

lemma pair_sq (i : A) : pair i * pair i=0 := last_square i i i

/-- inserting all psi_i bar_i; any further such factor vanishes -/
theorem pair_vol_zero {i : A} {s : Finset A} (h : i ∈ s) : pair i * vol s=0 := by
  classical
  rw [← insert_erase h, vol_step (s.erase i) i (notMem_erase i s),← mul_assoc,pair_sq,zero_mul]

theorem top_power (s : Finset A) : (∑ i ∈ s, pair i)^s.card = (Nat.factorial s.card) • vol s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let n := s.card
    let y := ∑ j ∈ s, pair j
    have he : y*vol s=0 := by unfold y; rw [sum_mul]; exact sum_eq_zero fun _ h => pair_vol_zero h
    have hn : y^(n+1)=0 := by rw [pow_succ', (show y^n=_ from ih), mul_smul_comm, he, smul_zero]
    have hu := (show Commute (pair i) y from (pair_grade i).central y |>.symm)
    have h (k : ℕ) : (pair i+y)^(k+1) = ((k+1:ℕ) • (pair i*y^k)) + y^(k+1) := by
      induction k with
      | zero => simp
      | succ k h =>
        rw [pow_succ _, h, add_mul,mul_add,mul_add, smul_mul_assoc, smul_mul_assoc]
        rw [mul_assoc,← (hu.pow_right _).eq,← mul_assoc,pair_sq,zero_mul,smul_zero,
          ← (hu.pow_right _).eq]
        rw [add_smul (R:=ℕ) (k+1) 1,one_smul,mul_assoc, ← pow_succ, pow_succ y (k+1)]; abel
    rw [sum_insert hi, card_insert_of_notMem hi, h, hn, add_zero]
    rw [(show y^(s.card)=_ from ih), mul_smul_comm, smul_smul, Nat.factorial_succ, vol_step s i hi]

end Saturate

namespace Onsite
variable {n : Side} {F : ℕ} (X : Support n)

def fill (X : Support n) (F : ℕ) : Insertion n F := ContinuousMap.const _ (vol (modes X F))

lemma top (U : Grid n) : Grass.Plus (fill X F U) := vol_plus _

lemma fill_commute (f : Insertion n F) : Commute f (fill X F) := by
  change f * _ = _*f; ext1 i; exact (top X i).central _

lemma fill_saturated : vol (modes X F) = ((Nat.factorial (modes X F).card : ℂ)⁻¹) •
    (form (offset (fun _ : Flavor F => (1:ℝ)) X))^(modes X F).card := by
  have ht : (Nat.factorial (modes X F).card : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  rw [expansion]; simp_rw [Complex.ofReal_one,one_smul]
  rw [Saturate.top_power, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ ht]

lemma fill_invariant : Lat.Invariant (fill X F) := by
  intro k; ext1 i; change slots F k (vol _) = vol _; rw [fill_saturated, map_smul, map_pow, invariant (fun _ : Flavor F => 1) X k]

lemma reachable_fill {S : Set (Site n)} (h : (X : Set (Site n)) ⊆ S) :
    vol (modes X F) ∈ (pass (setDay (F:=F) S)).range := by
  rw [fill_saturated]
  apply Subalgebra.smul_mem; apply Subalgebra.pow_mem; exact reachable _ h

lemma floors_fill (F : ℕ) {S : Set (Site n)} (h : (X : Set (Site n)) ⊆ S) : Floors S (fill X F) := by
  obtain ⟨a,H⟩ := reachable_fill (F:=F) X h
  exact ⟨fun _ => a,continuous_const,(fun _ _ _ => rfl),fun U => H.symm⟩

variable (C : Cells.Cut n)
def mirror : Equiv.Perm (Modes n F) := (Equiv.prodCongr (Equiv.prodCongr (perm C) (Equiv.refl Fiber)) (Equiv.refl _))

lemma mapped_modes : (modes X F).map (mirror (F:=F) C).toEmbedding = modes (opposite C X) F := by
  ext i; rw [mem_map_equiv, mem_modes, mem_modes, mem_opposite]; rfl

lemma reflected_fill {P : Cut n F} : RP.picture C P (fill X F) = fill (opposite C X) F := by
  unfold picture
  let t := mount C P
  have he (Y : Support n) : t.roll (fill Y F)=fill Y F := by
    ext1 U; change t.tape F (vol _) = vol _; rw [fill_saturated,map_smul,map_pow,taped];
  rw [he]; have h : reflect C (fill X F)=fill (opposite C X) F := by
    ext1 i; change theta C (vol _) = vol _
    have ht (x : Fields n F) (k : ℕ) : theta C (x^k)=(theta C x)^k := by
      induction k with
      | zero => simp [theta]
      | succ k ih => rw [pow_succ,theta_mul,ih,pow_succ']
    have hc : (modes (opposite C X) F).card = (modes X F).card := by rw [← mapped_modes, card_map]
    rw [fill_saturated X, fill_saturated, map_smulₛₗ,ht,reflected,hc]; simp
  rw [h,he]
end Onsite
end YM.Massive
