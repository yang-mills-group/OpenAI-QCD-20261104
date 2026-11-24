import YM.Analysis.MomentPD
import Mathlib.MeasureTheory.Integral.Pi
/-! # sample positivity needs no continuity if diagonal integrable too -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Function Set MeasureTheory Filter YM.Analysis
open scoped Topology ComplexOrder
variable {X : Type*} [MeasurableSpace X]
variable {K : X → X → ℂ} {μ : Measure X}
variable (P : Integrable (fun x : X × X => K x.1 x.2) (μ.prod μ)) (S : Integrable (fun x => K x x) μ)
section
variable [IsProbabilityMeasure μ]
-- single via cursor decomposition
lemma iid (n : ℕ) (i j : Fin (n+1)) (h:i≠j) : MeasurePreserving (fun x : Fin (n+1) → X => (x i,x j)) (Measure.pi (fun _ => μ)) (μ.prod μ) := by
   obtain ⟨k,rfl⟩:= Fin.exists_succAbove_eq (Ne.symm h) -- check
   exact ((MeasurePreserving.id μ).prod (measurePreserving_eval (fun _ => μ) k)).comp (measurePreserving_piFinSuccAbove (α:=fun _=>X) (fun _=> μ) i)
include S P
lemma pairs (n : ℕ) (i j : Fin (n+1)) :
    Integrable (fun x : Fin (n+1)→ X => K (x i) (x j)) (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin (n+1)→ X, K (x i) (x j) ∂Measure.pi (fun _ => μ)) = (if i=j then ((∫ x,K x x ∂μ)-(∫ x : X × X,K x.1 x.2 ∂μ.prod μ)) else 0) + ∫ x : X × X,K x.1 x.2 ∂μ.prod μ := by
   by_cases h : i=j
   · subst j; let f(x:X):= K x x
     have hu : MeasurePreserving (fun x : Fin (n+1)→ X => x i) (Measure.pi (fun _ => μ)) μ:=measurePreserving_eval _ _
     refine ⟨hu.integrable_comp_of_integrable S,?_⟩; rw [if_pos rfl,sub_add_cancel]; change _=∫ x, f x ∂μ
     have he:= integral_map hu.aemeasurable (f:=f) (by rw [hu.map_eq]; exact S.aestronglyMeasurable); rw [hu.map_eq] at he; exact he.symm
   have hu:=iid (μ:=μ) n i j h; let f (x:X × X):= K x.1 x.2
   refine ⟨hu.integrable_comp_of_integrable P,?_⟩; rw [if_neg h,zero_add]; have he:=integral_map hu.aemeasurable (f:=f) (by rw [hu.map_eq]; exact P.aestronglyMeasurable); rw [hu.map_eq] at he; exact he.symm
lemma flock (H:NNKernel K) : 0 ≤ ∫ x : X×X,K x.1 x.2 ∂μ.prod μ := by
    let J:=∫ x : X×X,K x.1 x.2 ∂μ.prod μ; let D:=(∫ x,K x x ∂μ)-J
    have hv (n:ℕ)(i: Fin (n+1)):(∫ x : Fin (n+1)→ X, ∑ j,K (x i) (x j) ∂Measure.pi (fun _ => μ)) = D+(n+1:ℕ) • J:=by
        rw [integral_finsetSum _ (fun j _=> (pairs P S n i j).1)]; simp_rw [(pairs P S n i _).2, Finset.sum_add_distrib]; simp [D,J]
    have hu (n:ℕ): 0 ≤ ((n+1:ℕ):ℂ)⁻¹* D + J:=by
         have hi : 0 ≤ ∫ x : Fin (n+1)→ X, ∑ i,∑ j,K (x i) (x j) ∂Measure.pi (fun _ => μ) := integral_nonneg fun x=> by simpa using H.positivity x (fun _ => 1)
         rw [integral_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=> (pairs P S n i j).1))] at hi
         simp_rw [hv, Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
         apply (mul_nonneg (show 0≤((((n+1:ℕ):ℂ)⁻¹)^2) from by positivity) hi).trans_eq
         field_simp -- check
    refine ge_of_tendsto (x:=atTop) (f:= fun n:ℕ=> ((n+1:ℕ):ℂ)⁻¹* D + J) ?_ (Eventually.of_forall hu)
    have hp : Tendsto (fun n:ℕ=> ((((n+1:ℕ):ℂ)⁻¹))) atTop (𝓝 0):=by
          simp_rw [show ∀ n:ℕ, (((n+1:ℕ):ℂ)⁻¹)=Complex.ofReal (((n+1:ℕ):ℝ)⁻¹) from fun i=>by push_cast; rfl] -- test
          rw [← Complex.ofReal_zero]
          have hi:Tendsto (fun n:ℕ=>n+1) atTop atTop:=tendsto_atTop_mono (fun n:ℕ=> (show n ≤ n+1 by omega)) (tendsto_id (x:=atTop)) -- test
          have ht:Tendsto (fun n:ℕ=> ((n+1:ℕ):ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp hi
          have he:Tendsto (fun n:ℕ=> (((n+1:ℕ):ℝ)⁻¹)) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp ht
          exact Complex.continuous_ofReal.continuousAt.tendsto.comp he
    simpa only [zero_mul,zero_add] using ((hp.mul_const D).add_const J)
end
end YM.QCD.Tide
