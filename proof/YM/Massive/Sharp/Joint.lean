import YM.Massive.Pressure.Selector
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Set Filter Function Complex Metric InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
open Disk
variable {M : Type*} (i0 : M) (F Y: M→ℂ→ℂ) (U L p:M→ℝ)
namespace Gravity
variable (hF:∀ i,Differentiable ℂ (F i))(hY:∀ i,DifferentiableOn ℂ (Y i) D ∧ContinuousOn (Y i) closedD)(hp:∀ i,0<p i)(hRel:∀ i x, F i x=(p i:ℂ)*F i0 x)
variable (h₀:∀ i z,z∈closedD→Y i z≠0)(hU:∀ i,0<U i)(hL:∀ i,0<L i)(ht:∀ i, ‖Y i 0‖ * L i ≤ ‖F i 0‖)(he:∀ i z,z∈closedD→ ‖F i z‖ ≤ ‖Y i z‖*U i)
abbrev question (x:ℝ)(y:ℝ):ℝ:= x*(y/x)^21
-- preserve power budgets identical in typography.Mode.Room denominator includes monomials cost.Depth.Free ticket $u scales$. choose F marker ζ tuned.
def expect (i : M)(x:ℂ) := F i x / (Y i x * (U i:ℂ))
include hF hY hp hRel h₀ hU hL ht he
set_option maxHeartbeats 520000 in
theorem align : ∃ x:ℝ,x∈Icc (1/2:ℝ) 1 ∧∀ i, ‖Y i x‖ *question (U i) (L i) ≤ ‖F i x‖:=by
    let D'(m:M)(x:ℂ):ℂ:= Y m x*(U m:ℂ)
    have hu m : (U m:ℂ)≠0:= by exact_mod_cast (hU m).ne'
    have hr m:ContinuousOn (D' m) closedD:=(hY m).2.mul continuousOn_const
    have h m x (h:x∈closedD): D' m x≠0:= mul_ne_zero (h₀ m x h) (hu m)
    have hN m z : ‖D' m z‖= ‖Y m z‖ * U m:=by unfold D'; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hU m).le]
    let f:= expect F Y U; have hh i z:‖f i z‖= ‖F i z‖/‖D' i z‖:=norm_div ..
    let g(m:M)(x:ℂ):= (p m:ℂ) *D' i0 x/D' m x;
    have hG: Joint i0 f g:=by
        refine ⟨fun i=> ⟨(hF i).differentiableOn.div ((hY i).1.mul (differentiable_const _).differentiableOn) (fun x hx=>h _ _ (open_closed hx)),(hF i).continuous.continuousOn.div (hr i) (h i),fun x hx=>?_⟩,fun i=>(continuousOn_const.mul (hr _)).div (hr _) (h i),fun m x hx=> div_ne_zero (mul_ne_zero (by exact_mod_cast (hp m).ne') (h _ _ hx)) (h _ _ hx),?_⟩
        · rw [hh]; exact (div_le_one (norm_pos_iff.mpr (h i x hx))).mpr ((he i x hx).trans_eq (hN i x).symm)
        intro m x hx; change F m x/D' m x=_*(F i0 x/D' i0 x); rw [hRel m x]; unfold g; field_simp [h _ _ hx]
    have h₁ i: 0<‖D' i 0‖:=norm_pos_iff.mpr (h _ _ zero_closed)
    have h₂ (i:M):L i/U i ≤ ‖f i 0‖:=by rw [hh]; apply (le_div_iff₀ (h₁ i)).2; rw [hN, show L i/U i*(‖Y i 0‖*U i)= ‖Y i 0‖* L i from by field_simp [(hU i).ne']]; exact ht i -- maybe rearrange
    obtain ⟨x,hx,hx'⟩:= hG.selects (norm_pos_iff.mp (lt_of_lt_of_le (div_pos (hL i0) (hU i0)) (h₂ _))); have hΨ: (x:ℂ)∈closedD:= by rw [closed, Complex.norm_real,Real.norm_of_nonneg (by linarith only [hx.1])]; linarith only [hx.2];
    refine ⟨x,hx,fun i=>?_⟩; have he:= (le_div_iff₀ (norm_pos_iff.mpr (h i (x:ℂ) hΨ))).mp ((pow_le_pow_left₀ (div_pos (hL i) (hU i)).le (h₂ i) 21).trans ((hx' i).trans_eq (hh ..))); unfold question; rw [hN] at he; linarith only [he]
end Gravity
end YM.Massive.Pressure
#print axioms YM.Massive.Pressure.Gravity.align
