import YM.Pods.Wander
/-! # Wide-margin Chess inequalities on continuous parity-homogeneous insertions
   Use margin(width longM or shorter allowed by neighborhood being probed).
   No assumed occupancy rank or direction for fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Chess.Fortuna
open Chess.Array QCD QCD.Lat QCD.Grass QCD.RP Lattice Wilson MeasureTheory Function Filter Finset Romance
open scoped BigOperators Topology Matrix.Norms.Frobenius ComplexOrder Classical
variable {A : Type*} {n : Side} {F : ℕ} {x y : Insertion n F}
variable {T:Cells.Tiling n}{R : Regulator n F}{r:ℕ}
structure Seal (V: Insertion n F→ₗ[ℂ]ℂ) (R:Regulator n F)(T:Cells.Tiling n)(k:ℕ):Prop where
   sewn (p:T.Cell)(a:Axis)(f g:Insertion n F)(hf:Floors (⋃ v∈T.plusCells p a,T.margin v k) f)(h:Invariant f)(hg:Floors (⋃ v∈T.plusCells p a,T.margin v k) g)(h':Invariant g): let w(x y:Insertion n F):= V (picture (T.bandCut p a) R.zeroCut x*y); ‖w f g‖^2 ≤ ‖w f f‖*‖w g g‖

structure Figure (R:Regulator n F)(T:Cells.Tiling n)(k:ℕ)(f:A→T.Cell→Insertion n F) :Prop extends Pattern R T f where
   more i p : Floors (T.margin p k) (f i p)

lemma figure_scale {T:Cells.Tiling n} {R:Regulator n F} {K:A→T.Cell→Insertion n F}{k:ℕ}(h:Figure R T k K)(u:A→ℝ): Figure R T k (fun i v => (u i:ℂ) • K i v):= ⟨Pattern.scale R T h.toPattern u, fun i v=> flooring_smul _ (h.more i v)⟩ -- arg
namespace Array
variable {K : A → T.Cell → Insertion n F} (C : T.Cell → A)
variable (hK : Figure R T r K)
variable (p:T.Cell)(a:Axis) (B:T.Cell → A) (V: Insertion n F→ₗ[ℂ]ℂ) (hp: Seal V R T r)
def costL (C : T.Cell → A) (K : A → T.Cell → Insertion n F) (V : Insertion n F→ₗ[ℂ]ℂ) := ‖V (use T univ.toList K C)‖


def rootL (V : Insertion n F→ₗ[ℂ]ℂ) (K : A → T.Cell → Insertion n F) (i : A) :=
    costL (fun _ => i) K V ^ (Fintype.card T.Cell : ℝ)⁻¹

theorem poweringL (i : A) : rootL (T:=T) V K i ^ (Fintype.card T.Cell) = costL (fun _ => i) K V := by
  unfold rootL; rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ costL (T:=T) (fun _ => i) K V from norm_nonneg _),
    inv_mul_cancel₀ (by exact_mod_cast T.cells_positive.ne'), Real.rpow_one]

lemma costL_scale (v : A→ℝ) (u : T.Cell → A) (h : ∀ i, 0 ≤ v i) :
    costL u (fun i a => (v i:ℂ) • K i a) V = (∏ i : T.Cell, v (u i)) * costL u K V := by
    have he : ((univ.toList.map (fun a : T.Cell => (v (u a):ℂ))).prod)=((∏ i : T.Cell, v (u i):ℝ) : ℂ):=by
       rw [Complex.ofReal_prod, prod_map_toList]
    have hp:= Finset.prod_nonneg (s:=(univ:Finset T.Cell)) (f:=fun i=>v (u i)) (fun i _=> h (u i))
    unfold costL; rw [use_scale,map_smul,norm_smul]; change ‖(univ.toList.map _).prod‖ * _ = _
    simp only [Function.comp_def]; rw [he,Complex.norm_real,Real.norm_of_nonneg hp]

include hK
lemma batches : Floors (⋃ y∈(T.plusCells p a),T.margin y r) (use T (T.plusCells p a).toList K C) ∧ Invariant (use T (T.plusCells p a).toList K C) := by
    generalize he : (T.plusCells p a).toList=l; have ht : ∀ i∈l,i∈ T.plusCells p a:=by simp [← he]
    clear he; induction l with
    | nil=> exact ⟨flooring_one,invariant_one⟩
    | cons i l ih=> obtain ⟨hL,h⟩:=ih (fun i hi=> ht i (List.mem_cons_of_mem _ hi)); exact ⟨flooring_mul (lower_maps (hK.more (C i) i) (by intro x hx; exact Set.mem_iUnion.2 ⟨i,Set.mem_iUnion.2 ⟨ht i (by simp),hx⟩⟩)) hL,invariant_mul _ _ (hK.invariant (C i) i) h⟩
omit hK in
lemma holds_period {x y : Insertion n F}(h:SignedEq x y):‖V x‖=‖V y‖:=by rcases h with h|h <;> simp [h]
include hp
lemma reflectingL : costL (T.assign p a C B) K V ^ 2 ≤ costL (T.assign p a B B) K V * costL (T.assign p a C C) K V := by
    obtain ⟨hx,h1⟩:= batches C hK p a; obtain ⟨hz,h2⟩:= batches B hK p a; unfold costL; rw [holds_period V (glued C hK.toPattern p a B),holds_period V (glued C hK.toPattern p a C),holds_period V (glued B hK.toPattern p a B)]
    exact hp.sewn p a _ _ hz h2 hx h1
-- purely combinatorial propagation. No special two-side, power-of-two geometry.
lemma maximizeL [Fintype A] [Nonempty A] : ∃ i : A, ∀ C : T.Cell → A, costL C K V ≤ costL (fun _ => i) K V := by
    classical
    let Xv (C : T.Cell → A) := costL C K V
    obtain ⟨B,hμb,H⟩:= Finset.exists_max_image univ Xv Finset.univ_nonempty
    let Q (C : T.Cell → A) := Xv C = Xv B
    have he : T.Reflects Q := by
      intro p a C hC
      let f := C ∘ T.mate p a
      have ht := reflectingL C hK p a f V hp
      rw [show T.assign p a C f = C from funext fun i=> by unfold Cells.Tiling.assign; split; rfl; simp [f] ] at ht
      let q:=Xv B
      let b:=Xv (T.assign p a C C)
      let u:=Xv (T.assign p a f f)
      have hb : b ≤ q:= H _ (mem_univ _)
      have hv : u ≤ q:= H _ (mem_univ _)
      have hpos : 0 ≤ b:= norm_nonneg _
      change Xv C ^ 2 ≤ u*b at ht
      rw [show Xv C = Xv B from hC] at ht
      change b=q
      apply le_antisymm hb
      rcases eq_or_lt_of_le (show 0 ≤ q from norm_nonneg _) with hx|hx
      · rwa [← hx]
      apply le_of_mul_le_mul_left _ hx
      exact (sq q) ▸ ht.trans (mul_le_mul_of_nonneg_right hv hpos)
    obtain ⟨i,Hi⟩:= T.existence Q he B rfl
    exact ⟨i,fun p => (H p (mem_univ _)).trans_eq (show Xv (fun _=>i)=Xv B from Hi).symm⟩

/-- Chessboard inequality for any parity-homogeneous replicated cells
(incl copying odd cells), once proven to replicate into each other by
actual link-reflections up to signs. -/
theorem operation [Fintype A] : costL C K V ≤ ∏ i : T.Cell, rootL V (T:=T) K (C i) := by
    classical
    have hf (i : A) : 0 ≤ rootL (T:=T) V K i := Real.rpow_nonneg (norm_nonneg _) _
    have he (ε : ℝ) (hε : 0 < ε) : costL C K V ≤ ∏ i : T.Cell, (rootL (T:=T) V K (C i)+ε):=by
      let r (i:A) := rootL (T:=T) V K i+ε
      have hr i : 0 < r i := add_pos_of_nonneg_of_pos (hf i) hε
      let u (i:A) := (r i)⁻¹
      let F i v := (u i:ℂ) • K i v
      haveI : Nonempty A := ⟨C 0⟩
      have hu i : 0 ≤ u i := (inv_pos.mpr (hr i)).le
      obtain ⟨i,hi⟩:= maximizeL (A:=A) (K:=F) (figure_scale hK u) V hp
      specialize hi C; unfold F at hi; rw [costL_scale V u _ hu, costL_scale V u _ hu, prod_const, card_univ, ← poweringL, ← mul_pow] at hi
      have hy : (u i * rootL V (T:=T) K i) ^ Fintype.card T.Cell ≤ 1 := by
        apply pow_le_one₀ (mul_nonneg (hu _) (hf _)); unfold u
        rw [inv_mul_eq_div]; exact (div_le_one (hr _)).mpr (lt_add_of_pos_right _ hε).le
      replace hi := hi.trans hy; unfold u at hi; rw [Finset.prod_inv_distrib,inv_mul_eq_div] at hi
      exact (div_le_one (prod_pos fun i _=> hr _)).mp hi
    have hx : Tendsto (fun ε : ℝ => ∏ i, (rootL (T:=T) V K (C i)+ε)) (𝓝[>] (0:ℝ))
        (𝓝 (∏ i, rootL (T:=T) V K (C i))) := by
      have ht : Continuous (fun ε : ℝ => ∏ i, (rootL (T:=T) V K (C i)+ε)) := by fun_prop
      simpa [ContinuousWithinAt] using ht.continuousAt.continuousWithinAt (x := 0) (s := Set.Ioi 0)
    exact ge_of_tendsto hx ((show ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε from self_mem_nhdsWithin).mono fun ε hx => he ε hx)
end Array
end YM.Massive.Chess.Fortuna
#print axioms YM.Massive.Chess.Fortuna.Array.operation
