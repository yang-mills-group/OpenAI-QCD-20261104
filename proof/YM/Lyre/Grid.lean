import YM.Lyre.Bores
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open QCD QCD.Lat QCD.Grass QCD.RP Lattice Wilson MeasureTheory Function Filter Finset
open Chess Tide
open scoped BigOperators Topology Matrix.Norms.Frobenius ComplexOrder
variable {A : Type*} {n : Side} {F : ℕ} {x y: Stud n F}
lemma signsM {w z: Stud n F} (h : SignedEq x y) (hp : SignedEq w z) : SignedEq (x*w) (y*z) := by
  rcases h with h|h <;> rcases hp with hp|hp <;> simp only [SignedEq,h,hp,neg_neg,neg_mul,mul_neg]; all_goals tauto
variable {C:Cells.Cut n}
lemma smog (a:ℂ)(x: Stud n F): tallH C (a • x) = star a • tallH C x:=by
    funext U; rw [huesT,Pi.smul_apply,map_smulₛₗ,Pi.smul_apply,huesT]; rfl
lemma smogOne:tallH C (1:Stud n F)=1:=by funext U; simp [huesT]
lemma coatM(x y: Stud n F): tallH C (x*y)=tallH C y * tallH C x:=by
    funext U; rw [huesT,Pi.mul_apply,Pi.mul_apply,huesT,huesT,tilt_mul]
variable (R : Regulator n F) (T : Cells.Tiling n)

def Potion (x : Stud n F) := ∃ p : Bool, ∀ U, Grass.Hom p (x U)
lemma Potion.swap (a b : Stud n F) (ha : Potion a) (hb : Potion b) : SignedEq (b*a) (a*b) := by
  obtain ⟨p,h⟩:=ha; obtain ⟨q,H⟩:=hb
  have he (V : Grid n) : (b*a) V = if p && q then -((a*b) V) else (a*b) V := Grass.Hom.swap (h V) (H V)
  cases e : p && q
  · apply Or.inl; funext V; simp only [he,e, Bool.false_eq_true, ↓reduceIte]
  apply Or.inr; funext V; simp only [he,e, ↓reduceIte, Pi.neg_apply]

structure Texture (R:Regulator n F) (T:Cells.Tiling n)(K : A → T.Cell → Stud n F) : Prop where
  floors (i v) : Plum.Fence (T.chamber v) (K i v)

  parity (i v) : Potion (K i v)
  moves p a i v : SignedEq (tallH (T.bandCut p a) (K i v)) (K i (T.mate p a v))

lemma Texture.scale {K : A → T.Cell → Stud n F} (h : Texture R T K) (u : A → ℝ) :
    Texture R T (fun i v => (u i:ℂ) • K i v) where
  floors i v := (h.floors i v).mass _
  parity i v := by obtain ⟨p,H⟩ := h.parity i v; exact ⟨p,fun U => (H U).smul _⟩
  moves p a i v := by
    rw [smog (C:=T.bandCut p a)]; rcases h.moves p a i v with h|h
    · apply Or.inl; simp [h]
    apply Or.inr; simp [h]

namespace Array
/-- Always use a List in the given order; restricted products are still
honest Grassmann products. -/
def use (l : List T.Cell) (K : A → T.Cell → Stud n F) (C : T.Cell → A) := (l.map fun i => K (C i) i).prod

variable {T R}
variable {K : A → T.Cell → Stud n F} (C : T.Cell → A)
variable (h : Texture R T K)

include h
lemma rearrange (l k : List T.Cell) (p : List.Perm l k) : SignedEq (use T l K C) (use T k K C) := by
  induction p with
  | nil => exact SignedEq.refl _
  | cons a _ ih => exact signsM (SignedEq.refl _) ih
  | swap a b l =>
    unfold use; simp only [List.map_cons,List.prod_cons, ← mul_assoc]
    exact signsM ((h.parity _ a).swap _ _ (h.parity _ b)) (SignedEq.refl _)
  | trans _ _ i j => exact SignedEq.trans i j

variable (p : T.Cell) (a : Axis)

lemma mirrored (l : List T.Cell) : SignedEq (tallH (T.bandCut p a) (use T l K C))
    (use T (l.reverse.map  (T.mate p a)) K (C ∘  (T.mate p a))) := by
    induction l with
    | nil => apply Or.inl; exact smogOne
    | cons x l ih =>
      have he := h.moves p a (C x) x
      unfold use at *; simp only [List.map_cons,List.prod_cons,coatM,List.reverse_cons,
        List.map_append,List.map_map,List.map_nil,List.prod_append, List.prod_nil, mul_one,
        Function.comp_apply, T.mate_invol] at ih ⊢ -- careful map_map
      apply signsM ih he

private lemma halfUse : Plum.Fence (T.bandCut p a).sector (use T (T.plusCells p a).toList K C) := by
  generalize he : (T.plusCells p a).toList=l
  have ht : ∀ i∈l, i∈ T.plusCells p a:=by simp [← he]
  clear he; induction l with
  | nil => exact Plum.Fence.one
  | cons v l ih =>
    have H:= ih fun i h => ht i (List.mem_cons_of_mem _ h)
    exact ((h.floors (C v) v).high (T.within p a v ((T.positive_side ..).mp (ht v (by simp))))).mult H

variable (B : T.Cell → A)

omit h
private lemma read_congr {n : Side} (T : Cells.Tiling n) {l : List T.Cell}
    (K : A → T.Cell → Stud n F) {R R' : T.Cell → A} (h : ∀ x∈l,R x=R' x) :
    use T l K R = use T l K R' := by
  unfold use; congr 1; apply List.map_congr_left; intro a ha; rw [h a ha]

private lemma reverses : List.Perm ((T.plusCells p a).toList.reverse.map  (T.mate p a)) (T.minusCells p a).toList := by
  have he := (show Involutive (T.mate p a) from T.mate_invol p a).injective
  refine (List.perm_ext_iff_of_nodup (List.Nodup.map he (by simp [Finset.nodup_toList])) (by simp [Finset.nodup_toList])).2 ?_
  intro i
  simp only [List.mem_map,List.mem_reverse,Finset.mem_toList]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact (T.cycles p a _).1 (by rw [T.mate_invol]; exact hj)
  intro hi
  exact ⟨_,(T.cycles p a i).mpr hi,T.mate_invol ..⟩

private lemma split : List.Perm (univ.toList : List T.Cell) ((T.minusCells p a).toList ++ (T.plusCells p a).toList) := by
  have ht (i : T.Cell) : i∈(T.minusCells p a).toList ↔ i ∉ (T.plusCells p a).toList := by
    simp only [Finset.mem_toList,T.negative]
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_append.mpr ?_)).2
  · intro i; simp only [List.mem_append,ht,Finset.mem_toList,Finset.mem_univ]; tauto
  refine ⟨?_,?_,?_⟩
  · exact Finset.nodup_toList _
  · exact Finset.nodup_toList _
  intro i hi j hj e; exact (ht i).mp hi (e.symm ▸ hj)

lemma use_append (l k : List T.Cell) : use T (l++k) K C=use T l K C * use T k K C:=by simp [use]

include h
lemma glued (p : T.Cell) (a : Axis) (B : T.Cell → A) : SignedEq (use T univ.toList K (T.assign p a C B))
    (tallH (T.bandCut p a) (use T (T.plusCells p a).toList K B) * use T (T.plusCells p a).toList K C) := by
  apply (rearrange _ h _ _ (split p a)).trans
  have he : use T (T.plusCells p a).toList K (T.assign p a C B)= use T (T.plusCells p a).toList K C := read_congr _ _ (by intro x hx; rw [Cells.Tiling.assign, if_pos (Finset.mem_toList.mp hx)])
  have hb : use T (T.minusCells p a).toList K (T.assign p a C B)= use T (T.minusCells p a).toList K (B ∘ T.mate p a):= read_congr _ _ (by intro x hx; rw [Cells.Tiling.assign, if_neg ((T.negative ..).1 (Finset.mem_toList.mp hx))]; rfl)
  rw [use_append,he,hb]
  exact signsM (((mirrored _ h p a _).trans (rearrange _ h _ _ (reverses p a))).symm) (SignedEq.refl _)

omit h
def cost (C : T.Cell → A) (K : A → T.Cell → Stud n F) (R : Regulator n F) := ‖valueH R (use T univ.toList K C)‖


lemma use_scale (u : A → ℂ) (l : List T.Cell) : use T l (fun i j => u i • K i j) C =
    ((l.map (u ∘ C)).prod) • use T l K C := by
  induction l with
  | nil => simp [use]
  | cons i t ih => unfold use at *; simp only [List.map_cons, List.prod_cons]
                   rw [ih,smul_mul_assoc,mul_smul_comm,mul_smul]; rfl

def root (R : Regulator n F) (K : A → T.Cell → Stud n F) (i : A) :=
    cost (fun _ => i) K R ^ (Fintype.card T.Cell : ℝ)⁻¹

theorem powering (i : A) : root (T:=T) R K i ^ (Fintype.card T.Cell) = cost (fun _ => i) K R := by
  unfold root; rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ cost (T:=T) (fun _ => i) K R from norm_nonneg _),
    inv_mul_cancel₀ (by exact_mod_cast T.cells_positive.ne'), Real.rpow_one]

lemma cost_scale (v : A→ℝ) (u : T.Cell → A) (h : ∀ i, 0 ≤ v i) :
    cost u (fun i a => (v i:ℂ) • K i a) R = (∏ i : T.Cell, v (u i)) * cost u K R := by
    have he : ((univ.toList.map (fun a : T.Cell => (v (u a):ℂ))).prod)=((∏ i : T.Cell, v (u i):ℝ) : ℂ):=by
       rw [Complex.ofReal_prod, prod_map_toList]
    have hp:= Finset.prod_nonneg (s:=(univ:Finset T.Cell)) (f:=fun i=>v (u i)) (fun i _=> h (u i))
    unfold cost; rw [use_scale,spend,norm_smul]; change ‖(univ.toList.map _).prod‖ * _ = _
    simp only [Function.comp_def]; rw [he,Complex.norm_real,Real.norm_of_nonneg hp]

variable (ht':R.t=0)(hk : T.kind = .link) (hβ : 0 ≤ R.β) (hn : 4 ≤ n.val)
include h ht' hk hβ hn

lemma reflecting : cost (T.assign p a C B) K R ^ 2 ≤ cost (T.assign p a B B) K R * cost (T.assign p a C C) K R := by
    have Hi:= halfUse C h p a; have H:= halfUse B h p a
    have he : 2 ≤ (T.bandCut p a).half.val := by have he := (T.bandCut p a).even; omega
    unfold cost; rw [signsV R (glued C h p a B), signsV R (glued C h p a C), signsV R (glued B h p a B)]
    have ht:= shears R ht' hβ H Hi hk he; unfold valueH; simp only [norm_mul]; dsimp only at ht
    nlinarith only [mul_le_mul_of_nonneg_left ht (sq_nonneg ‖R.Z⁻¹‖)]

-- purely combinatorial propagation. No special two-side, power-of-two geometry.
lemma maximize [Fintype A] [Nonempty A] : ∃ i : A, ∀ C : T.Cell → A, cost C K R ≤ cost (fun _ => i) K R := by
    classical
    let V (C : T.Cell → A) := cost C K R
    obtain ⟨B,hp,H⟩:= exists_max_image univ V Finset.univ_nonempty
    let Q (C : T.Cell → A) := V C = V B
    have he : T.Reflects Q := by
      intro p a C hC
      let f := C ∘ T.mate p a
      have ht := reflecting C h p a f ht' hk hβ hn
      rw [show T.assign p a C f = C from funext fun i=> by unfold Cells.Tiling.assign; split; rfl; simp [f] ] at ht
      let q:=V B
      let b:=V (T.assign p a C C)
      let u:=V (T.assign p a f f)
      have hb : b ≤ q:= H _ (mem_univ _)
      have hv : u ≤ q:= H _ (mem_univ _)
      have hpos : 0 ≤ b:= norm_nonneg _
      change V C ^ 2 ≤ u*b at ht
      rw [show V C = V B from hC] at ht
      change b=q
      apply le_antisymm hb
      rcases eq_or_lt_of_le (show 0 ≤ q from norm_nonneg _) with hx|hx
      · rwa [← hx]
      apply le_of_mul_le_mul_left _ hx
      exact (sq q) ▸ ht.trans (mul_le_mul_of_nonneg_right hv hpos)
    obtain ⟨i,Hi⟩:= T.existence Q he B rfl
    exact ⟨i,fun p => (H p (mem_univ _)).trans_eq (show V (fun _=>i)=V B from Hi).symm⟩

/-- Chessboard inequality for any parity-homogeneous replicated cells
(incl copying odd cells), once proven to replicate into each other by
actual link-reflections up to signs. -/
theorem tiles [Fintype A] : cost C K R ≤ ∏ i : T.Cell, root R (T:=T) K (C i) := by
    classical
    have hf (i : A) : 0 ≤ root (T:=T) R K i := Real.rpow_nonneg (norm_nonneg _) _
    have he (ε : ℝ) (hε : 0 < ε) : cost C K R ≤ ∏ i : T.Cell, (root (T:=T) R K (C i)+ε):=by
      let r (i:A) := root (T:=T) R K i+ε
      have hr i : 0 < r i := add_pos_of_nonneg_of_pos (hf i) hε
      let u (i:A) := (r i)⁻¹
      let F i v := (u i:ℂ) • K i v
      haveI : Nonempty A := ⟨C 0⟩
      have hu i : 0 ≤ u i := (inv_pos.mpr (hr i)).le
      obtain ⟨i,hi⟩:= maximize (A:=A) (K:=F) (Texture.scale _ _ h u) ht' hk hβ hn
      specialize hi C; unfold F at hi; rw [cost_scale u _ hu, cost_scale u _ hu, prod_const, card_univ, ← powering, ← mul_pow] at hi
      have hy : (u i * root R (T:=T) K i) ^ Fintype.card T.Cell ≤ 1 := by
        apply pow_le_one₀ (mul_nonneg (hu _) (hf _)); unfold u
        rw [inv_mul_eq_div]; exact (div_le_one (hr _)).mpr (lt_add_of_pos_right _ hε).le
      replace hi := hi.trans hy; unfold u at hi; rw [Finset.prod_inv_distrib,inv_mul_eq_div] at hi
      exact (div_le_one (prod_pos fun i _=> hr _)).mp hi
    have hx : Tendsto (fun ε : ℝ => ∏ i, (root (T:=T) R K (C i)+ε)) (𝓝[>] (0:ℝ))
        (𝓝 (∏ i, root (T:=T) R K (C i))) := by
      have ht : Continuous (fun ε : ℝ => ∏ i, (root (T:=T) R K (C i)+ε)) := by fun_prop
      simpa [ContinuousWithinAt] using ht.continuousAt.continuousWithinAt (x := 0) (s := Set.Ioi 0)
    exact ge_of_tendsto hx ((show ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε from self_mem_nhdsWithin).mono fun ε hx => he ε hx)
end Array
end YM.Massive.Lyre

#print axioms YM.Massive.Lyre.Array.tiles
