import YM.QCD.Nola.Rain
import YM.Push.ABSOLUTE_SUMS.Clusters

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Ursell
open Trees Graph RG Lattice Relation Finset
open scoped BigOperators Classical Topology
variable {ι : Type*} (R : ι → ι → Prop) {n : Side}
variable (X : ι → Support n)

def chargeCard (w : ι → ℝ) (a : ℝ) (i : ι) := w i * Trees.currencyCard a (X i)

lemma charge_posCard {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℝ) (i : ι) :
    0 ≤ chargeCard X w a i := mul_nonneg (hw _) (Real.exp_pos _).le

private lemma test_noneCard (ht : Tests R X) (m : ℕ) (z : Tuple ι m) (w u : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) (a : ℝ) :
    atVertex R (chargeCard X w a) (chargeCard X u a) none z ≤
      ∑ p : Fin m → Option (Fin m), rootWCard X w u a ⟨m,indexRoot z p⟩ := by
  let W := chargeCard X w a; let U := chargeCard X u a
  have hg := Graph.pay (pot R z)
  let P (p : Fin m → Option (Fin m)) : Prop := Graph.sprouts (pot R z) p
  let o := ∏ i : Option (Fin m), if i=none then U (z i) else W (z i)
  have he : o=U (z none)*∏ i : Fin m, W (z (some i)) := by simp [o,Fintype.prod_option]
  have hb : 0 ≤ o := he ▸ mul_nonneg (charge_posCard X hu ..) (prod_nonneg fun i _ => charge_posCard X hw ..)
  change |coefficient R z| * o/m.factorial ≤ _
  calc
    _ ≤ (∑ p, if P p then (1:ℝ) else 0)*o/m.factorial := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hg hb) (by positivity)
    _ ≤ _ := by
      rw [sum_mul,sum_div]; apply sum_le_sum; intro i _; split
      next h =>
        unfold rootWCard forestWCard; dsimp only; rw [forestWeightCard,if_pos (spanned R X ht h),Fintype.card_fin,
          he,one_mul,mul_div_assoc]; exact le_rfl
      next h => simpa only [zero_mul,zero_div] using rootW_nonnegCard X hw hu a ⟨m,indexRoot z i⟩

private lemma indexRoot_injCard {m : ℕ} : Function.Injective
    (fun p : Tuple ι m × (Fin m → Option (Fin m)) => indexRoot p.1 p.2) := by
  rintro ⟨z,p⟩ ⟨w,q⟩ h
  have hp : p=q := congr_arg (fun x => x.2.1) h
  suffices he : z=w by rw [he,hp]
  funext i; cases i with
  | none => exact congr_arg (fun x => x.1) h
  | some j => exact congr_arg (fun x : RootAt ι m => x.2.2 j) h

private lemma budget_noneCard (ht : Tests R X) {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : ReadyCard X w a γ δ q) (he : SumBudget (chargeCard X u (a+δ)) b)
    (m : ℕ) : SumBudget (fun z : Tuple ι m => atVertex R (chargeCard X w a) (chargeCard X u a) none z)
      (b*q^m) := by
  have hw := h.2.2.2.2.1
  have hh := budget_pull _ (@indexRoot_injCard ι m) (root_atCard X hu h he m)
  let f := fun p : Tuple ι m × (Fin m → Option (Fin m)) => rootWCard X w u a ⟨m,indexRoot p.1 p.2⟩
  refine budget_of_sum (fun z => atVertex_pos R (charge_posCard X hw a) (charge_posCard X hu a) none z)
    fun s => ?_
  calc
    _ ≤ ∑ z∈s, ∑ p, f (z,p) := sum_le_sum fun z _ => test_noneCard R X ht m z w u hw hu a
    _ = ∑ i∈s ×ˢ univ, f i := by rw [sum_product]
    _ ≤ _ := budget_sum hh _

lemma budget_rootCard (ht : Tests R X) {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : ReadyCard X w a γ δ q) (he : SumBudget (chargeCard X u (a+δ)) b)
    (m : ℕ) (i : Option (Fin m)) :
    SumBudget (fun z : Tuple ι m => atVertex R (chargeCard X w a) (chargeCard X u a) i z) (b*q^m) := by
  let e := Equiv.swap i none
  let W := chargeCard X w a; let U := chargeCard X u a
  have he' : Function.Injective (fun z : Tuple ι m => z ∘ e) := fun z p h => by
    funext i; obtain ⟨i,rfl⟩ := e.surjective i; exact congr_fun h i
  have eq (z : Tuple ι m) : atVertex R W U i z = atVertex R W U none (z ∘ e) := by
    unfold atVertex
    rw [relabel R e z]; congr 2
    symm; apply Fintype.prod_equiv e; intro j
    by_cases h : j=none
    · rw [h]; simp [e]
    have he : e j ≠ i := by rw [← show e none=i by simp [e]]; exact e.injective.ne h
    simp only [h,he,↓reduceIte,Function.comp_apply]
  simp_rw [show ∀ z : Tuple ι m, atVertex R (chargeCard X w a) (chargeCard X u a) i z = _ from eq]
  exact budget_pull _ he' (budget_noneCard R X ht hu h he m)

theorem cluster_atCard (ht : Tests R X) {w : ι → ℝ} {a γ δ q b : ℝ} (Q : ι → Prop)
    (h : ReadyCard X w a γ δ q) (he : SumBudget (chargeCard X (marked Q w) (a+δ)) b) (m : ℕ) :
    SumBudget (fun z : Tuple ι m => if ∃ i, Q (z i) then clusters R (chargeCard X w a) z else 0)
      (b*q^m) := by
  let V := Option (Fin m)
  let W := chargeCard X w a; let u := marked Q w; let U := chargeCard X u a
  have hw := h.2.2.2.2.1; have hw' := charge_posCard X hw a
  have hu := marked_pos Q hw; have hu' := charge_posCard X hu a
  let n : ℝ := (m:ℝ)+1
  have hn : 0 < n := by unfold n; positivity
  have hb := budget_scale (show 0 ≤ n⁻¹ by positivity) (budget_over univ
    (fun (i : Option (Fin m)) z => atVertex R W U i z) (fun _ => b*q^m)
    (fun i _ => budget_rootCard R X ht hu h he m i))
  have hc : SumBudget (fun z : Tuple ι m => n⁻¹ * ∑ i : Option (Fin m), atVertex R W U i z)
      (b*q^m) := budget_loosen hb (by unfold n; simp; apply le_of_eq; field_simp)
  -- once z hits, one possible root i suffices; after sum use all of them.
  refine budget_mono hc (fun i => ?_) fun i => ?_
  · split
    next h => exact clusters_nonneg R hw' i
    next h => exact le_rfl
  split
  next h =>
    obtain ⟨j,hj⟩ := h
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (fun a _ =>
      atVertex_pos R hw' hu' a i) (mem_univ j)) (by positivity))
    have he : U (i j)=W (i j) := by simp only [U,W,u,chargeCard,marked,if_pos hj]
    unfold atVertex clusters
    rw [prod_congr rfl (show ∀ a ∈ (univ:Finset V),
      (if a=j then U (i a) else W (i a)) = W (i a) from fun a _ => by
          split
          · subst a; exact he
          · rfl),
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    unfold W n
    apply le_of_eq; ring_nf; field_simp; ring
  next h => exact hc.1 i

theorem cluster_tailCard (ht : Tests R X) {w : ι → ℝ} {a γ δ q b : ℝ} (Q : ι → Prop)
    (h : ReadyCard X w a γ δ q) (he : SumBudget (chargeCard X (marked Q w) (a+δ)) b) (m : ℕ) :
    SumBudget (fun z : Clusters ι => if m ≤ z.1 then (if ∃ i, Q (z.2 i) then
      clusters R (chargeCard X w a) z.2 else 0) else 0) (b*q^m*(1-q)⁻¹) := by
  -- work around potential distinct `Classical.decEq` instances
  apply sigma_tail (fun z : Clusters ι => if ∃ i, Q (z.2 i) then clusters R (chargeCard X w a) z.2 else 0)
    (fun k => cluster_atCard R X ht Q h he k) (budget_nonneg he) (ready_posCard X h).le
    h.2.2.2.1 m


end YM.Push.AbsoluteSums.Ursell
