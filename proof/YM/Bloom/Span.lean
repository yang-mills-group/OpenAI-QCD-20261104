import YM.Bloom.Rip
/-! # Price bounding under warrants, abstract delivery supports post. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom.Span
open Function Lattice Laurent Bloch Metric RG Filter Arise
open Finset YM.Bank Precision
open scoped Topology BigOperators
variable {H K F W: Type*}[NormedAddCommGroup F][NormedSpace ℝ F] {ℓ r j k:ℕ}
variable (L:H→ Parc→ₗ[ℝ] F) (m:H→ℝ) (G: Filter H)
-- ? missing variable inference.
lemma fellow {l j:ℕ}(hm:∀ᶠ x in G, 0 ≤ m x) (h:∀ (w:List Axis), l ≤ w.length → w.length ≤ j→ ∀ x:Cover,∃ C:ℝ,0 ≤ C∧∀ᶠ i in G,‖L i (strike w x)‖ ≤ C*m i) (X:Parc)(hx:X∈tails l j): ∃ C:ℝ,0 ≤ C∧∀ᶠ i in G,‖L i X‖ ≤ C*m i:=by
      refine Submodule.span_induction (p:=fun x _=>∃ C:ℝ, 0 ≤ C ∧∀ᶠ i in G,‖L i x‖ ≤ C*m i) ?_ ⟨0,le_rfl,Eventually.of_forall fun i=>by rw [map_zero,norm_zero,zero_mul]⟩ ?_ ?_ hx
      · rintro z ⟨w,a,hw,hv,rfl⟩; exact h _ hw hv _
      · rintro x y _ _ ⟨C,hc,h⟩ ⟨D,hd,ht⟩; refine ⟨C+D,add_nonneg hc hd,?_⟩; filter_upwards [h,ht] with i hx hy; rw [map_add,add_mul]; exact (norm_add_le ..).trans (add_le_add hx hy)
      rintro i x _ ⟨C,hc,h⟩; refine ⟨‖i‖*C, by positivity,?_⟩; filter_upwards [h] with t ht; rw [map_smul,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
lemma payments (M:H→Parc→Parc→F)(hL:H→Parc→ Parc→ₗ[ℝ] F)(hR:H→Parc→ Parc→ₗ[ℝ] F)(he:∀ i X Y,hL i Y X=M i X Y)(hu:∀ i X Y,hR i X Y=M i X Y)(hm:∀ᶠ i in G,0≤ m i) (h:∀ (w:List Axis), ℓ ≤ w.length→ w.length ≤j→∀ v (s:List Axis), r ≤ s.length→ s.length≤k→ ∀ x:Cover,∃ C:ℝ,0 ≤ C∧∀ᶠ i in G,‖M i (strike w v) (strike s x)‖ ≤ C*m i) (X:Parc)(hx:X∈tails ℓ j)(Y:Parc)(hy:Y∈tails r k): ∃ C:ℝ,0≤ C ∧∀ᶠ i in G,‖M i X Y‖ ≤ C*m i:=by
     simp_rw [← he]; refine fellow (fun i=> hL i Y) m G hm (fun w hw hf v=>?_) _ hx; simp_rw [he,← hu]; refine fellow (fun i=> hR i (strike w v)) m G hm (fun s hr hq z=>?_) _ hy; simpa only [hu] using h _ hw hf _ _ hr hq _
lemma fund {G:Filter H} (P:H→F)(g:H→ℝ) : (∀ᶠ i in (⊤: Filter H), ‖P i‖ ≤ g i) ↔ ∀ i, ‖P i‖ ≤ g i:= eventually_top
end YM.Bloom.Span
#print axioms YM.Bloom.Span.fellow
#print axioms YM.Bloom.Span.payments
