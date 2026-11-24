import YM.Intag.Shift
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open Lattice Function Set Filter Finset
open scoped Topology
variable {n : Side} (T : Tiling n)
lemma pass_weights {m : ℕ} (i : Axis) (x : Fin m → Site n) (K : Fin m→ℕ) (h : (∑ s, 2*K s)<T.side.val) :
    ∃ v : Per n, ∀ s, let r := (x s i-v).val % T.side.val
                      K s ≤ r ∧ r+K s < T.side.val := by
  classical
  let A (s : Fin m) := T.hom (x s i)
  let B (s:Fin m) : Per T.side → Prop := fun v => K s ≤ v.val ∧ v.val+K s < T.side.val
  suffices he : ∃ y : Per T.side, ∀ s, B s (A s-y) by
    obtain ⟨y,h⟩ := he
    refine ⟨↑y.val,fun s => ?_⟩
    have hx := h s
    unfold B at hx
    have hz (t : Per n) : T.hom t = ↑t.val := calc
      _ = T.hom (↑t.val) := by rw [ZMod.natCast_zmod_val]
      _ = _ := map_natCast ..
    have hv : A s-y = T.hom ((x s i)-(y.val:Per n)) := by rw [map_sub,map_natCast, ZMod.natCast_zmod_val]
    rw [hv,hz (x s i-_), ZMod.val_natCast] at hx; exact hx
  let bad (s:Fin m) := ((range (K s)).image ((↑) : ℕ→Per T.side)) ∪ ((range (K s)).image fun i : ℕ => (↑(T.side.val-(i+1)):Per T.side))
  have he (s:Fin m) {y} (ht : y∉bad s) : B s y := by
    rcases lt_or_ge y.val (K s) with g|g
    · exact (ht (mem_union_left _ (mem_image.mpr ⟨y.val,mem_range.mpr g,ZMod.natCast_zmod_val _⟩))).elim
    refine ⟨g,?_⟩; by_contra! hq
    have hm := y.val_lt
    exact ht (mem_union_right _ (mem_image.mpr ⟨T.side.val - (y.val+1), mem_range.mpr (by omega),by simp [show T.side.val-(T.side.val-(y.val+1)+1) = y.val by omega,Per]⟩))
  let W := Finset.univ.biUnion fun i : Fin m => (bad i).image fun b => A i-b
  have hx : W.card < Finset.univ.card := calc
    _ ≤ ∑ i : Fin m,((bad i).image fun b => A i-b).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin m, 2*K i := Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (show (bad i).card ≤ 2*K i by
      unfold bad; apply (Finset.card_union_le ..).trans
      rw [two_mul]
      apply add_le_add _ _ <;> exact Finset.card_image_le.trans (card_range (K i) |>.le))
    _ < (Finset.univ (α := Per T.side)).card := by simpa [Per] using h
  obtain ⟨y,-,hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hx
  refine ⟨y,fun i => he i fun H => hy ?_⟩
  exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨_,H,sub_sub_cancel ..⟩⟩

lemma fits_weight {m : ℕ} (x : Fin m → Site n) (K : Fin m→ℕ) (hk : ∀ s:Fin m, 0<K s) (h : (∑ s, 2*K s)<T.side.val) :
    ∃ o : Site n, ∀ s, x s∈(T.newly o).margin ((T.newly o).which (x s)) (K s) := by
  choose o ho using fun (i : Axis) => T.pass_weights i x K h
  refine ⟨o,fun v => ?_⟩
  let B := T.newly o
  change x v∈B.margin (B.which (x v)) (K v)
  have he (i : Axis) : K v ≤ B.coordinated (B.which (x v)) (x v) i ∧ B.coordinated (B.which (x v)) (x v) i+K v < B.side.val := by rw [Tiling.residual]; exact ho i v
  refine ⟨fun i => ?_,fun i => ⟨(he i).1,?_⟩⟩
  · have hh := he i
    have hP:=hk v
    change B.kind.Strict B.side.val (B.coordinated _ _ _)
    cases B.kind <;> unfold Kind.Strict <;> omega
  have hh := he i
  have ht : B.kind.shift ≤ 1 := by cases B.kind <;> unfold Kind.shift <;> decide
  omega

end YM.Cells.Tiling
#print axioms YM.Cells.Tiling.fits_weight
