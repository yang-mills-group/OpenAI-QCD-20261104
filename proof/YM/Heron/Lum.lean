import YM.Heron.Fawn
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad)
variable (A:TinG)(hc:TrueC A)(i j k:Axis)(p:E4)(t:ℝ)(ht:0<t)
variable (D₀: Faces){U:Set E4}(hU:IsOpen U) (g:Spins) (v:Drive) (χ:E4→ℝ) (hw: Way A U g)(hv: Seam v)(hs:tsupport χ⊆U)(hχ:ContDiff ℝ ∞ χ)(Hχ:HasCompactSupport χ)(x:E4)
noncomputable def tiers(A:TinG)(v:Drive)(g:Spins)(χ:E4→ℝ)(D₀:Faces)(i:Axis)(x:E4):ℂ:=
   (χ x * v i x) • dotL D₀ (g x)+(∑ j:Axis,(χ x* v j x) • dotL D₀ (cog A i (cog A j (g x))))
noncomputable def aura (v:Drive)(g:Spins)(χ:E4→ℝ)(D₀:Faces)(x:E4):ℂ:=∑ i:Axis, (χ x * v i x) • dotL D₀ (Maxwell.grad i g x)
local notation "F"=> bz A p t D₀
local notation "K"=> axon p t
local notation "Y"=> tiers A v g χ D₀
local notation "V"=> aura v g χ D₀
noncomputable def vale (A:TinG)(v:Drive)(g:Spins)(χ:E4→ℝ)(D₀:Faces)(x:E4):ℂ:= -aura v g χ D₀ x-∑ i:Axis, grad i (tiers A v g χ D₀ i) x
local notation "M"=> vale A v g χ D₀
include hw hc hv ht hU hs
lemma bastion : χ x • (∑ i:Axis, grad i (brook A F g v i) x) = -(K x • V x)+ ∑ i:Axis, grad i K x • Y i x:=by
    by_cases hx:x∈ tsupport χ; swap; · simp [tiers,aura,image_eq_zero_of_notMem_tsupport hx]
    rw [baptism A hc p D₀ t ht hU g x (hs hx) hw v hv] -- inspect order hf
    simp only[tiers,aura,Finset.smul_sum, smul_add,smul_smul, neg_smul,smul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib];
    simp_rw [mul_comm (grad _ _ x), ← mul_assoc, mul_comm (K x) (χ x),add_assoc]; simp_rw [mul_assoc (χ x) _ _,mul_comm (K x) (v _ _)]
    apply congr_arg; apply congr_arg; rw [Finset.sum_comm]
omit hc ht hU
include hχ Hχ
private lemma bulb (q:E4→ℂ)(he:∀ x,x∈ U→ ContDiffAt ℝ ∞ q x) : let Q:=fun x=> (χ x*v i x) • q x; ContDiff ℝ ∞ Q ∧ HasCompactSupport Q := by
     intro Q; refine ⟨contDiff_iff_contDiffAt.mpr fun x=> ?_, (HasCompactSupport.mul_right (f':=v i) Hχ).smul_right (f':=q)⟩ -- API
     by_cases hx:x∈ tsupport χ; · exact (hχ.contDiffAt.mul (hv.smooth i).contDiffAt).smul (he x (hs hx))
     refine (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq ?_; filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy; rw [show Q y=(χ y*v i y) • q y from rfl, show χ y=0 from hy]; simp
lemma skyY :ContDiff ℝ ∞ (Y i) ∧ HasCompactSupport (Y i):=by
    let f:=fun x=> (χ x*v i x) • dotL D₀ (g x); let q(j:Axis)(x:E4):ℂ:= (χ x* v j x) • dotL D₀ (cog A i (cog A j (g x))); have hp:ContDiff ℝ ∞ f ∧ HasCompactSupport f:=bulb A i g _ _ hw hv hs hχ Hχ _ fun x hx=> (dotL D₀).contDiff.contDiffAt.comp x (hw.live x hx);
    have he(j): ContDiff ℝ ∞ (q j) ∧ HasCompactSupport (q j):= bulb A j g _ _ hw hv hs hχ Hχ _ fun x hx=> (dotL D₀).contDiff.contDiffAt.comp x ((cog A i).contDiff.contDiffAt.comp x ((cog A j).contDiff.contDiffAt.comp x (hw.live x hx))); rw [show Y i=f + ∑ j:Axis,q j from funext fun x=>by simp [tiers,f,q]]; rw [Fin.sum_univ_four]; exact ⟨hp.1.add ((((he 0).1.add (he 1).1).add (he 2).1).add (he 3).1), hp.2.add ((((he 0).2.add (he 1).2).add (he 2).2).add (he 3).2)⟩
lemma skyV :ContDiff ℝ ∞ V ∧ HasCompactSupport V:=by
    let f(j:Axis)(x:E4):ℂ:=(χ x * v j x) • dotL D₀ (grad j g x); have hp(i):ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i):=bulb A i g v χ hw hv hs hχ Hχ _ fun x hx=> (dotL D₀).contDiff.contDiffAt.comp x (Maxwell.grad_smooth i (hw.live x hx) (by simp)); rw[show V= ∑ i:Axis,f i from funext fun x=>by simp [aura,f]]; rw [Fin.sum_univ_four]; exact ⟨(((hp 0).1.add (hp 1).1).add (hp 2).1).add (hp 3).1, (((hp 0).2.add (hp 1).2).add (hp 2).2).add (hp 3).2⟩
end YM.Heron
#print axioms YM.Heron.bastion
#print axioms YM.Heron.skyY
