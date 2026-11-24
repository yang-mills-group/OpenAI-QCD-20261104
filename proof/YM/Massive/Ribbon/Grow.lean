import YM.Massive.Ribbon.Indices
/-!
# Weight caps on polynomial/exterior substitution stencils
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset
open QCD QCD.Lat Lattice Grass
open scoped BigOperators Topology Matrix ComplexOrder TensorProduct Classical
variable {d : ℕ}

namespace Rim
variable {A : Type*} [Fintype A] (v:A→ℕ)
def grains (A: Type*)[Fintype A](v:A→ℕ)(k:ℕ) : Submodule ℂ (Alg A):=⨅ s:Finset A,⨅ (_:∑ i∈s,v i≠k), LinearMap.ker (coef s)
lemma grain_test (x:Alg A)(k:ℕ): x∈grains A v k ↔ ∀ s:Finset A,(∑ i∈s,v i)≠ k →coef s x=0:=by simp [grains]
variable {k l:ℕ}
lemma mon (s:Finset A)(he:k=∑ i∈s,v i):Grass.mono s∈grains A v k:= (grain_test ..).mpr (fun t h=>read_other t s (fun hx=>h (hx ▸ he.symm)))
lemma payroll {x y:Alg A}(hx:x∈grains A v k)(hy:y∈grains A v l): x*y∈grains A v (k+l):=by
   rw [← Grass.write x,← Grass.write y]; simp_rw [sum_mul, mul_sum]; apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _
   by_cases h₁:∑ j∈i,v j=k; swap; · rw [(grain_test v x k).mp hx i h₁,zero_smul,zero_mul]; exact Submodule.zero_mem _
   by_cases h₂:∑ i∈j,v i=l; swap; · rw [(grain_test v y l).mp hy j h₂,zero_smul,mul_zero]; exact Submodule.zero_mem _
   by_cases he:Disjoint i j; swap; · rw [smul_mul_assoc,mul_smul_comm, Grass.mono_mul_zero _ _ he,smul_zero,smul_zero]; exact Submodule.zero_mem _
   rw [smul_mul_assoc,mul_smul_comm]; apply Submodule.smul_mem _ _; apply Submodule.smul_mem _ _; rcases Grass.mono_mul_sign i j he with h|h <;> rw [h]; apply mon v _; rw [Finset.disjUnion_eq_union,sum_union he,h₁,h₂]; apply Submodule.neg_mem; apply mon v _; rw [disjUnion_eq_union,sum_union he,h₁,h₂]
lemma grains_atom (i:A): atom i ∈ grains A v (v i):= by rw [← mono_single]; exact mon v _ (by simp)
lemma alphabet_grade {T :Alg A →ₐ[ℂ] Alg A}(he:∀ i,T (atom i)∈grains A v (v i))(s:Finset A):T (mono s) ∈ grains A v (∑ i∈s,v i):=by
    induction s using Finset.induction_on with
    | empty=>rw [mono_empty,map_one,← mono_empty]; exact mon v _ rfl
    | @insert i s h ih=>
       have hf:Disjoint {i} s:=by simp [h]
       have hx:=Grass.mono_mul_sign {i} s hf; rw [mono_single,disjUnion_eq_union,singleton_union] at hx; rw [sum_insert h]; rcases hx with h|h; · rw [← h,map_mul]; exact payroll v (he i) ih
       apply (Submodule.neg_mem_iff _).mp; rw [← map_neg, ← h, map_mul]; exact payroll v (he i) ih
lemma keeps {M:Matrix A A ℂ}(hp:∀ i j,v i≠v j→ M i j=0)(s:Finset A): changeVars M (mono s) ∈ grains A v (∑ i∈s,v i):=by
    apply alphabet_grade v; intro i; rw [change_atom]; apply Submodule.sum_mem; intro j _; by_cases h:v i=v j; · rw [h]; exact Submodule.smul_mem _ _ (grains_atom v j)
    rw [hp i j h,zero_smul]; exact Submodule.zero_mem _
lemma dkeeps (s:Finset A)(n:ℕ)(he:n=∑ i∈s,v i): dagger (mono s)∈ grains A v n:=by
    subst n; induction s using Finset.induction_on with
    | empty=>rw [mono_empty, dagger_one,←mono_empty]; exact mon _ _ rfl
    | @insert i s h ih=> have hf:Disjoint {i} s:=by simp [h]
                         have hh:= mono_mul_sign _ _ hf; rw [mono_single,disjUnion_eq_union,singleton_union] at hh; rw [sum_insert h,add_comm]; rcases hh with H|H
                         · rw [← H,dagger_mul,dagger_atom]; exact payroll v ih (grains_atom v i)
                         apply (Submodule.neg_mem_iff _).mp; rw [←map_neg,← H, dagger_mul, dagger_atom]; exact payroll v ih (grains_atom v i)
lemma step{f: Alg A→ₗ[ℂ]Alg A}(he:∀ s:Finset A,f (mono s)∈ grains A v (∑ i∈s,v i)){x:Alg A}(hp:x∈grains A v k): f x∈grains A v k:=by
   rw [← Grass.write x,map_sum]; apply Submodule.sum_mem; intro i _; by_cases h: (∑ p∈i,v p)= k; · rw [map_smul]; exact Submodule.smul_mem _ _ (h ▸ he i)
   rw [(grain_test ..).mp hp i h,zero_smul,map_zero]; exact Submodule.zero_mem _
end Rim
open TensorProduct
variable {h : ℕ}
lemma pay_gen (p : PowerPair d)(hp:weight p≤d): gen p∈cap d := Submodule.subset_span ⟨p,hp,rfl⟩
lemma launch (i:Powers)(s:Finset (Pairs (SpinMode d)))(x:ℂ)(h:UV.weight (i,s) ≤ d): (MvPolynomial.monomial i x) ⊗ₜ[ℂ] mono s∈cap d:=by
   suffices he:(MvPolynomial.monomial i x) ⊗ₜ[ℂ] mono s=x • gen (i,s) by exact he.symm ▸ (cap d).smul_mem x (pay_gen _ h)
   change _= x • (MvPolynomial.monomial i 1) ⊗ₜ[ℂ] mono s; rw [TensorProduct.smul_tmul', ←map_smul,smul_eq_mul,mul_one]
lemma pumpG (x:GPol)(s:Finset (Pairs (SpinMode d)))(hx:∀ t∈x.support, UV.weight (t,s) ≤ d): x ⊗ₜ[ℂ] mono s∈cap d:=by
    nth_rw 1 [MvPolynomial.as_sum x]; rw [sum_tmul]; exact Submodule.sum_mem _ (fun i hi=> launch _ _ _ (hx i hi))
lemma pump (x:GPol)(y:SpinPol d)(H: y∈Rim.grains _ letterWeight h) (hx:∀ t∈x.support, 2*Labels.height t+h ≤ d): x ⊗ₜ[ℂ] y∈cap d:=by
    rw [←Grass.write y, tmul_sum]; apply Submodule.sum_mem; intro s _; by_cases hh:(∑ i∈s,letterWeight i)=h; swap; · rw [(Rim.grain_test ..).mp H s hh,zero_smul,tmul_zero]; exact Submodule.zero_mem _
    rw [tmul_smul]; apply Submodule.smul_mem; exact pumpG _ s (fun t ht=> by simpa only [weight,hh] using hx t ht)
lemma billups (e : (i : ℕ) → Module.End ℝ (Labels.Taylor su i))(d aj:ℕ) (x: Powers)(h: 2*Labels.height x+aj ≤ d) : ∀ t∈ (Labels.changed e (MvPolynomial.monomial x 1)).support, 2*Labels.height t+aj ≤ d:=by
   intro v hv; have he: Labels.height v=Labels.height x := Labels.pure_moved (fun i=> i+2) e x 1 (MvPolynomial.mem_support_iff.mp hv); rw [he]; exact h
lemma cabin {T:Pol d→ₗ[ℂ]Pol d}(f:∀ x:PowerPair d, weight x≤d → T (gen x)∈cap d)(x:Pol d)(h:x∈cap d) : T x∈cap d:=by
    refine Submodule.span_induction (p:=fun x _=> T x ∈ cap d) (fun x hx=>?_) ?_ ?_ ?_ h -- parameter likely p lower
    · obtain ⟨p,hp,h⟩:=hx; rw [← h]; exact f p hp -- prefers exact?
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro _ _ _ _ he ht; rw [map_add]; exact Submodule.add_mem _ he ht
    intro c x _ h; rw [map_smul]; exact Submodule.smul_mem _ c h
-- generic step regular preserving any spin caps.
lemma changeCap (M: Matrix (Pairs (SpinMode d)) (Pairs (SpinMode d)) ℂ)(hp:∀ i j,letterWeight i ≠ letterWeight j → M i j=0)(e : (i:ℕ)→ Module.End ℝ (Labels.Taylor su i))(x:Pol d)(h:x∈cap d) : TensorProduct.map (Labels.changed e).toLinearMap (changeVars M).toLinearMap x ∈ cap d:=by
     apply cabin _ x h; intro p he; unfold gen; rw [TensorProduct.map_tmul]; exact pump _ _ (Rim.keeps letterWeight hp p.2) (billups e _ _ _ he)
end YM.Massive.UV
#print axioms YM.Massive.UV.changeCap
