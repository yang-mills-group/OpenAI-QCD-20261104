import YM.Pods.Shingle
import YM.Cells.Margins
import YM.Cells.Packing



/-!
# Finer centered grid inside arbitrary tiling

Site seams too. Compare using TRUE lattice rotations. Odd small widths.
For the axis bracketing use a vertical congruence family with bias depending
on seams. Distinguish being a smaller-grid center from fitting the big cells.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Cells.Spiro
open YM.Cells
open Lattice Function Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder

variable {c l:Side}(g:Ratio c l) (T:Tiling l)
open YM.Massive.Romance
def biasFor : ℕ := T.kind.shift * (g.count.val / 2)

def homeFor : Site l := fun i => T.base i + (biasFor g T:ℕ)

/-- All small center points relative to offset `o`. -/
def onCenters (G:Even c.val)(o : Site l) := {x | ∃ v, x=(mural g G o).copyMap v o}

/-- Native grid for contiguous component coordinates. -/
def OnGrid (a : Axis) (q : Per l) := ∃ z : ℤ, q = (homeFor g T) a + ((z:ℤ):Per l) * (g.count.val : ℕ)

variable (G:Even c.val)(P:Odd g.count.val)
include G P
lemma belongs {x : Site l} : x∈onCenters g G (homeFor g T) ↔ ∀ a, OnGrid g T a (x a) := by
  let o := homeFor g T
  let H := mural g G o
  constructor
  · rintro ⟨v,hv⟩ a
    refine ⟨(lift (n := c) v) a,?_⟩
    rw [hv,tuned g G P]; unfold Ratio.embed; simp [wrap, mul_comm]
  intro hG
  choose z hz using fun a => hG a
  let v := wrap (c) z
  refine ⟨v,?_⟩
  rw [tuned g G P]
  unfold v
  rw [Ratio.embed_wrap]; ext1 i
  rw [hz]
  dsimp only [wrap]; simp [ mul_comm]

lemma turns {x : Site l} (hx : x∈onCenters g G (homeFor g T))
    (hd : g.count.val ∣ T.side.val) (v : T.Cell) : T.copyMap v x∈onCenters g G (homeFor g T) := by
  let d := g.count.val
  let b := biasFor g T
  obtain ⟨q,hq⟩ := hd
  rw [belongs _ T G P]; intro i
  obtain ⟨z,hz⟩ := (belongs g T G P).mp hx i
  have ho : T.starts v i=T.base i+ ((v i).val:ℕ)*((T.side.val:ℕ): Per l) := by
    dsimp only [Tiling.starts]; simp only [Pi.add_apply, T.mount,Nat.cast_mul]
  have hy : T.starts v i=T.base i+ ((↑((v i).val*q : ℕ)) : Per l)*d := by
    rw [ho,hq]; push_cast; dsimp [d]; ring
  have ht := T.copy_formula v x i
  rw [hy,hz] at ht
  split_ifs at ht with he
  · have hw : T.kind.shift + 2*b = T.kind.shift*d := by
      obtain ⟨l, hl⟩ := P
      have hs : d/2=l := by dsimp [d];omega
      dsimp only [b,biasFor]
      change T.kind.shift+ 2*(T.kind.shift*(d/2))=_
      rw [hs, show d=2*l+1 from hl]; ring
    refine ⟨(((v i).val*q:ℕ):ℤ) + q - T.kind.shift - z,?_⟩
    rw [sub_eq_iff_eq_add.mp ht,hq]
    have ha := congr_arg (fun x : ℕ => (x:Per l)) hw
    unfold homeFor; unfold d b at *
    push_cast at *
    linear_combination -ha
  refine ⟨(((v i).val*q:ℕ):ℤ)+z,?_⟩
  rw [sub_eq_iff_eq_add.mp ht]; dsimp only [homeFor]
  push_cast; unfold d; ring

-- any sufficiently interior offset can be bracketed by TWO nearby columns on
-- this axis grid. Need margin w (smaller cell) at EVERY intermediate translate.
-- no accidental data about witnesses other than that one axis changed.
lemma bracket (w : Site l) (hx : w∈T.margin 0 (3*g.count.val)) (i : Axis) :
    let d := g.count.val
    ∃ v : ℕ → Site l, ∃ j : ℕ, j ≤ d ∧ v j=w ∧
    (∀ l ≤ d, v l ∈ T.margin 0 (2 * d)) ∧ (∀ l, l+1 ≤ d → v (l+1)=v l+step i) ∧
      (∀ l a, a≠i → v l a=w a) ∧ OnGrid g T i (v 0 i) ∧ OnGrid g T i (v d i) := by
  intro d
  let b := biasFor g T
  let r := T.coordinated 0 w i
  have hr := show 3*d≤r from hx.2 i |>.1
  have ht := show r+3*d+T.kind.shift≤T.side.val from hx.2 i |>.2
  have hk : 0<d := g.count.property
  have hi : b≤d := by unfold b biasFor; change T.kind.shift*(d/2)≤_; cases T.kind <;> simp [Kind.shift,Nat.div_le_self]
  let t := r-b
  let f := t/d
  let j := t%d
  have hh : j<d := Nat.mod_lt _ hk
  have he : b+f*d+j=r := by
    rw [Nat.add_assoc, show f*d+j=t from Nat.div_add_mod' ..]; dsimp only [t];omega
  let v (l : ℕ) := update w i (T.base i+((↑(b+f*d+l): Per _)))
  have hb (s) (l : ℕ) (H : s≠i) : v l s=w s := by simp [v,H]
  have hp (l : ℕ) (hl : l ≤ d) : T.coordinated 0 (v l) i=b+f*d+l := by
    unfold v Tiling.coordinated
    rw [update_self,T.starts_zero,add_sub_cancel_left]
    have hz := T.narrow
    apply ZMod.val_natCast_of_lt; omega
  refine ⟨v,j, hh.le,?_,fun l hl => ?_, fun l hl => ?_, fun l a ha => hb a l ha, ⟨(f:ℤ),?_⟩,⟨((f+1:ℕ):ℤ),?_⟩⟩
  · have hC := T.indent 0 w i; rw [T.starts_zero] at hC
    simp_rw [v,he]; rw [show T.base i+_ = _ from hC]; exact Function.update_eq_self _ _
  · have he := hp l hl
    have hu : 2*d ≤ T.coordinated 0 (v l) i := by omega
    have hw : T.coordinated 0 (v l) i+(2*d)+T.kind.shift ≤ T.side.val := by omega
    refine ⟨fun a => ?_,fun a => ?_⟩
    · by_cases e:a=i; subst a
      · change T.kind.Strict _ (T.coordinated 0 _ i)
        cases T.kind <;> unfold Kind.Strict <;> omega
      rw [hb _ _ e]; exact hx.1 a
    by_cases e:a=i; subst a
    · exact ⟨hu,hw⟩
    have hv := hx.2 a
    rw [show T.coordinated 0 (v l) a=T.coordinated 0 w a by unfold Tiling.coordinated; rw [hb _ _ e]]
    change 3*d ≤ _ ∧ T.coordinated 0 w a+3*d+_ ≤ _ at hv; omega
  · ext1 a; by_cases hu : a=i
    · subst a; simp [v]; ring
    simp [hb a _ hu,hu]
  · simp [v,homeFor]; dsimp only [b,d];ring
  simp [v,homeFor]; dsimp only [b,d];ring
end YM.Cells.Spiro
#print axioms YM.Cells.Spiro.turns
