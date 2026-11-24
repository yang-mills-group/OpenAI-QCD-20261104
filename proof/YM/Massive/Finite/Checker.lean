import YM.Massive.Finite.Minors
import YM.Massive.Finite.Chess

/-!
# Checkerboard of occupied sites at the cutoff

When every nearest-neighbor hop touches an occupied site, there is a
particularly simple **exact** formula for the expectation. No estimate
involving the sizes of the fermi interaction or inverse matrices on a sea.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Checker
open QCD QCD.RP QCD.Lat QCD.Grass Lattice Wilson Finset MeasureTheory Function
open scoped BigOperators Matrix.Norms.Frobenius ComplexOrder Topology

variable {n : Side} {F : ℕ} (X : Support n) (R : Regulator n F)

def Covers : Prop := ∀ x : Site n, x ∈ Xᶜ → ∀ a : Axis, x+step a ∈ X ∧ x-step a ∈ X

open Onsite

variable (h : Covers X)

include h

lemma covered_row (i j : Row n) (hi : i.1∈ Xᶜ) (hj : j.1∈ Xᶜ) (U : Grid n) (m : ℝ) :
    bareD R.t U m i j = if i=j then (↑(m+4):ℂ) else 0 := by
  have hh (a : Axis) : singleHop R.t U a i j=0 := by
    rw [hop_read,if_neg,if_neg,add_zero]
    · intro e; exact mem_compl.mp hj (e ▸ (h _ hi a).2)
    intro e; exact mem_compl.mp hj (e ▸ (h _ hi a).1)
  unfold bareD; rw [Matrix.add_apply, Matrix.sum_apply]
  by_cases he : i=j
  · rw [if_pos he]; simp only [Matrix.smul_apply, Matrix.sub_apply,Matrix.one_apply,if_pos he, hh]; simp [Axis]
  simp [hh,he]

lemma minor_entries (U : Grid n) (i j : Modes n F) (hi : i ∈ (modes X F)ᶜ) (hj : j ∈ (modes X F)ᶜ) :
    R.D U i j = if i=j then ((R.m i.2:ℂ)+4) else 0 := by
  simp only [mem_compl,mem_modes] at hi hj; unfold Regulator.D; rw [Matrix.blockDiagonal_apply]
  split
  next hb =>
    rw [covered_row X R h _ _ (mem_compl.mpr hi) (mem_compl.mpr hj)]
    split
    next he => simp [Prod.ext he hb]
    next ht => simp [show i≠j from fun e => ht (by rw [e])]
  next ht => simp [show i≠j from fun e => ht (by rw [e])]

omit h

def volumeMass : ℝ := ∏ i : Flavor F, (R.m i + 4)^12

lemma openModes (F : ℕ) : (modes X F)ᶜ = (Xᶜ ×ˢ univ) ×ˢ univ := by ext i; simp

private lemma diagonal_value {A : Type*} [Fintype A] [DecidableEq A] (w : Finset A) (D : Matrix A A ℂ) (g : A→ℂ) (H : ∀ i∈wᶜ,∀ j∈wᶜ, D i j=if i=j then g i else 0) :
    ber A (gauss D * vol w) = ∏ i ∈ wᶜ, g i := by
  rw [Saturate.minor_value, ← Finset.prod_coe_sort]
  have he : Saturate.minor D w=Matrix.diagonal (fun i : ↥wᶜ => g i):=by
    ext i j; rw [Matrix.diagonal_apply,Saturate.minor,Matrix.submatrix_apply,H i i.property j j.property]; simp
  rw [he,Matrix.det_diagonal]

include h
lemma measure (U : Grid n) : ber (Modes n F) ((R.density * fill X F) U) =
    (↑(bare R.β U * volumeMass R ^ (Xᶜ).card) : ℂ) := by
  rw [ContinuousMap.mul_apply,Regulator.density_apply,smul_mul_assoc,map_smul];
  change (_:ℂ)*ber _ (gauss _ * vol (modes X F)) = _
  rw [diagonal_value (modes X F) _ (fun i => (R.m i.2:ℂ)+4) (fun i hi j hj=>minor_entries X R h U i j hi hj),Complex.ofReal_mul]; congr 1
  unfold volumeMass
  simp only [Complex.ofReal_pow,Complex.ofReal_prod,Complex.ofReal_add,Complex.ofReal_ofNat]
  rw [openModes,prod_product]; change ∏ _x ∈ Xᶜ ×ˢ (univ:Finset Fiber), (∏ i:Flavor F, ((R.m i:ℂ)+4)) = _
  rw [prod_const, Finset.card_product, card_univ, ← Finset.prod_pow, ← prod_pow, show Fintype.card Fiber=12 by simp [Fiber,Pinor,Hue]]
  simp_rw [← pow_mul,mul_comm _ ((Xᶜ).card)]

lemma expectation : R.raw (fill X F) = (↑(Wilson.partition su n R.β * volumeMass R ^ (Xᶜ).card):ℂ) := by
  change (∫ U, _ ∂prior su n) = _; simp_rw [measure X R h]
  rw [integral_complex_ofReal, integral_mul_const]; rfl

omit h

lemma volumeMass_nonneg : 0 ≤ volumeMass R := prod_nonneg fun _ _ => Even.pow_nonneg (by decide : Even 12) _

lemma volumeMass_positive (H : ∀ i, R.m i + 4 ≠ 0) : 0 < volumeMass R := prod_pos fun i _ => Even.pow_pos (by decide : Even 12) (H i)

variable {X R}

/-- specialized tiling with link planes and unit width -/
abbrev tiling {n l : Side} (h : n.val=2*l.val) : Cells.Tiling n := {
  period := n
  units := ⟨1, by simp⟩
  widthHalf := l
  even := h
  kind := .link
  base := 0 }

variable {l : Side} (he : n.val=2*l.val)
local notation "Tʳ" => tiling he
include he

lemma belongs (v : Site n) : v ∈ (Tʳ).chamber v := by
  have hv : (Tʳ).starts v=v:=by unfold Cells.Tiling.starts; change 0 + wrap n ((1:ℕ) • lift v) = v; simp
  intro i; rw [hv]; change (v i-v i).val<1; rw [sub_self,ZMod.val_zero]; exact zero_lt_one

lemma mirror (v p : Site n) (a : Axis) : (Tʳ).mate p a v=((Tʳ).bandCut p a).reflect v := by
  funext i
  by_cases h : i=a
  · subst i
    have hv : (Tʳ).starts p=p:=by unfold Cells.Tiling.starts; change 0 + wrap n ((1:ℕ) • lift p) = p; simp
    rw [Cells.Tiling.mate_here];
    change _ = ((Tʳ).bandCut p a).reflect v ((Tʳ).bandCut p a).pos; rw [Cells.Cut.reflect_here];
    change _ = 2 * ((Tʳ).starts p) a - ↑Cells.Kind.link.shift-v a; rw [hv]; simp [Cells.Kind.shift]
  rw [Cells.Tiling.mate_off _ _ _ _ h,Cells.Cut.reflect_there ((Tʳ).bandCut p a) v h]

def color (he : n.val=2*l.val) (v : Site n) : ZMod 2 := ∑ i, (tiling he).parity (v i)

def black (he : n.val=2*l.val) : Support n := univ.filter (fun i => color he i=0)

lemma sunny (v : Site n) (a : Axis) : color he (v+step a)=color he v+1 ∧
    color he (v-step a)=color he v-1:=by
  have ht : (∑ i : Axis, (Tʳ).parity ((step a : Site n) i))=1 := by
    rw [sum_eq_single a];
    · simp [tiling] -- inspect
    · intro b _ h; simp [h,tiling]
    simp
  unfold color; simp only [Pi.add_apply, Pi.sub_apply]
  have hw (x y : Per n) : (Tʳ).parity (x+y) = (Tʳ).parity x + (Tʳ).parity y := (Tʳ).parity_add x y
  have hs (x y : Per n) : (Tʳ).parity (x-y) = (Tʳ).parity x - (Tʳ).parity y := (Tʳ).parity_sub x y
  simp_rw [hw,hs, Finset.sum_add_distrib, Finset.sum_sub_distrib, ht]; simp

omit he in
private lemma binary (v : ZMod 2) (h : v ≠ 0) : v = 1 := by fin_cases v <;> simp [ZMod] at h ⊢
lemma opposites (x : Site n) (a : Axis) : x+step a∈ black he ↔ x∈(black he)ᶜ := by
  rw [mem_compl]; simp only [black, mem_filter,mem_univ,true_and, (sunny he x a).1]
  by_cases h : color he x=0
  · rw [h]; decide
  rw [binary _ h]; decide
lemma covers : Covers (black he) := by
  intro x hx a
  have hh : color he x ≠ 0 := by simpa [black] using hx
  exact ⟨(opposites he x a).mpr hx,by simp [black,(sunny he x a).2,binary _ hh]⟩

lemma half_colors : (black he).card=((black he)ᶜ).card := by
  have ht : black he=((black he)ᶜ).map (Equiv.addRight (step (0:Axis))).toEmbedding := by
    ext i; rw [mem_map_equiv];
    obtain ⟨j,rfl⟩ := (Equiv.addRight (step (0:Axis))).surjective i
    rw [Equiv.symm_apply_apply]; exact opposites he j 0
  exact (congr_arg Finset.card ht).trans (Finset.card_map ..)

lemma double : (black he).card*2 = Fintype.card (Tʳ).Cell := by
  have ht := half_colors he; rw [card_compl] at ht
  have hv := card_le_univ (black he); change #(black he)*2=Fintype.card (Site n); omega
omit he

end YM.Massive.Checker
