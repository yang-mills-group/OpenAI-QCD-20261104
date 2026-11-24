import Mathlib.Analysis.Normed.Group.Tannery
import YM.QCD.Gas.Purse
import YM.Push.ABSOLUTE_SUMS.Log


/-! # Banach hard-core extension with clusters. See Gauge scalar counterparts -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.GasP
open Push.AbsoluteSums Gas NormedSpace
open Function Filter Graph Ursell Coef Trees RG Finset Lattice
open scoped BigOperators Classical Topology
variable {ι K : Type*}[NormedCommRing K][NormOneClass K][NormedAlgebra ℝ K][NormedAlgebra ℚ K][CompleteSpace K] (R : ι → ι → Prop) (w : ι → K)

def termP (z : Clusters ι) : K := ((z.1+1).factorial:ℝ)⁻¹ • (coefficient R z.2 • ∏ i,w (z.2 i))
def logS := ∑' i,termP R w i
def totalP := ∑' s,valueP R w s
lemma normStep (z: Clusters ι) : ‖termP R w z‖ ≤ ‖Gas.term R (fun i=>‖w i‖) z‖:=by
   unfold termP Gas.term
   rw [norm_smul,norm_smul, norm_div, norm_mul]; simp only [norm_inv, Real.norm_natCast] -- edit
   let k:= z.1
   have hp: ‖∏ i,w (z.2 i)‖ ≤ ∏ i, ‖w (z.2 i)‖:=norm_prod_le _ _
   rw [Real.norm_of_nonneg (show 0 ≤ ∏ i,‖w (z.2 i)‖ from prod_nonneg fun _ _=> norm_nonneg _), div_eq_inv_mul]; gcongr
section absol
variable {n : Side} (X : ι → Support n) (B : ℕ) (ht : Tests R X) (hX : ∀ i,(X i).Nonempty) {a γ δ q : ℝ}
variable (ha : 0 ≤ a) (h : Ready X B (fun i => ‖w i‖) a γ δ q)
include ht hX ha h
lemma absoluteS : SumBudget (fun z:Clusters ι=> ‖termP R w z‖) (((n.val^4:ℕ)*γ)*(1-q)⁻¹):= budget_mono (Gas.absolute _ _ _ _ ht hX ha (show Ready X B (fun i=> ‖(‖w i‖:ℝ)‖) a γ δ q from by simpa only [norm_norm])) (fun _=> norm_nonneg _) (normStep R w)
lemma absoluteR (m:ℕ) : SumBudget (fun z:Tuple ι m=> ‖termP R w ⟨m,z⟩‖) (((n.val^4:ℕ)*γ)*q^m):= budget_mono (Gas.absolute_at _ _ _ _ ht hX ha (show Ready X B (fun i=> ‖(‖w i‖:ℝ)‖) a γ δ q from by simpa only [norm_norm]) m) (fun _=> norm_nonneg _) (fun i=> normStep R w _)
end absol


lemma logRow_open [Fintype ι] (n : ℕ) : logRow R w n = ∑ z : Tuple ι n, termP R w ⟨n,z⟩ := by
  unfold logRow GasP.linked termP; rw [Finset.smul_sum]

lemma finite_log [Fintype ι] (hr : Hard R) {n : Side} (X : ι → Support n) (B : ℕ)
    (ht : Tests R X) (hX : ∀ i,(X i).Nonempty) {a γ δ q : ℝ} (ha : 0 ≤ a)
    (h : Ready X B (fun i => ‖w i‖) a γ δ q) : NormedSpace.exp (logS R w) = totalP R w := by
  have he : Summable (termP R w) := (absoluteS R w X B ht hX ha h).2.1.of_norm
  have hz : logS R w= ∑' i, logRow R w i := by
    unfold logS; rw [he.tsum_sigma]; apply tsum_congr; intro i
    rw [logRow_open, tsum_fintype]
  rw [hz,totalP,tsum_fintype (valueP R w)]
  let C : ℝ := (n.val^4:ℕ)*γ
  have hh := h.1
  refine exact_polynomial R w hr (show 0≤C by unfold C; positivity) (ready_pos X B h) h.2.2.2.1 ?_
  intro i; rw [logRow_open]
  exact (norm_sum_le ..).trans (budget_sum (absoluteR R w X B ht hX ha h i) univ)

-- restricting labels
abbrev chosenRel (D : Finset ι) := fun i j : ↥D => R i.val j.val
abbrev chosenW (D : Finset ι) := fun i : ↥D => w i.val

private def liftIndex (D : Finset ι) (i : Clusters ↥D) : Clusters ι := ⟨i.1,fun j => (i.2 j).val⟩
private def boundTo (D : Finset ι) (i : Clusters ι) : K := if ∀ j, i.2 j∈D then termP R w i else 0

private lemma actual (D : Finset ι) : ∑' i, boundTo R w D i = logS (chosenRel R D) (chosenW w D) := by
  unfold logS
  have he : Injective (liftIndex D) := by
    rintro ⟨s,p⟩ ⟨t,q⟩ h
    have hs : s=t := congr_arg Sigma.fst h; subst t
    have hi : (fun i => (p i).val) = (fun i => (q i).val) := (Sigma.mk.inj h).2 |> eq_of_heq
    have hp : p=q := funext fun i => Subtype.ext (congr_fun hi i)
    subst q; rfl
  have hr : Function.support (boundTo R w D) ⊆ Set.range (liftIndex D) := by
    rintro ⟨s,p⟩ hi
    have hi : ∀ j, p j∈D := by
      by_contra hn
      exact hi (if_neg hn)
    exact ⟨⟨s,fun i => ⟨p i,hi i⟩⟩,rfl⟩
  rw [← he.tsum_eq hr]; apply tsum_congr; rintro ⟨s,p⟩
  unfold boundTo liftIndex; dsimp only; rw [if_pos (fun j => (p j).property)]; unfold termP coefficient; rfl

private def pickedFrom (D : Finset ι) (s : Finset ι) : K := if s ⊆ D then valueP R w s else 0

private lemma literal (D : Finset ι) : ∑' i, pickedFrom R w D i = totalP (chosenRel R D) (chosenW w D) := by
  let f (i : Finset ↥D) : Finset ι := i.image (fun j => j.val)
  have hf : Injective f := Finset.image_injective Subtype.val_injective
  have hg : Function.support (pickedFrom R w D) ⊆ Set.range f := by
    intro i hi
    have he : i ⊆ D := by by_contra hh; exact hi (if_neg hh)
    let s : Finset ↥D := univ.filter (fun j => j.val∈i)
    refine ⟨s,?_⟩; ext j; rw [show f s=_ from rfl,mem_image]; constructor
    · rintro ⟨a,ha,rfl⟩; exact (mem_filter.mp ha).2
    intro h; exact ⟨⟨j,he h⟩, mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  have he (s : Finset ↥D) : pickedFrom R w D (f s) = valueP (chosenRel R D) (chosenW w D) s := by
    have hs : f s⊆ D := fun i hi => by obtain ⟨j,hj,rfl⟩ := mem_image.mp hi; exact j.property
    have he : separated (chosenRel R D) s ↔ separated R (f s) := by
      constructor
      · intro h i hi j hj hk
        obtain ⟨i,hi',rfl⟩ := mem_image.mp hi
        obtain ⟨j,hj',rfl⟩ := mem_image.mp hj
        exact h _ hi' _ hj' (fun hz => hk (congr_arg Subtype.val hz))
      intro h i hi j hj hk
      exact h _ (mem_image_of_mem _ hi) _ (mem_image_of_mem _ hj) (fun h => hk (Subtype.ext h))
    unfold pickedFrom valueP; rw [if_pos hs]
    by_cases hh : separated (chosenRel R D) s
    · rw [if_pos hh,if_pos (he.mp hh)]
      exact Finset.prod_image Subtype.val_injective.injOn
    rw [if_neg hh,if_neg fun h => hh (he.mpr h)]
  unfold totalP; rw [← hf.tsum_eq hg]; exact tsum_congr he

lemma actual_values {n : Side} (X : ι → Support n) (B : ℕ) (hX : ∀ i,(X i).Nonempty)
    {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Ready X B (fun i => ‖w i‖) a γ δ q) :
    SumBudget (fun s => ‖valueP R w s‖) (Real.exp ((n.val^4:ℕ)*γ)) := by
  let f (i : ι) := ‖w i‖
  have he := Product.everyone_ne X B (show ∀ i,0 ≤ f i from fun _ => norm_nonneg _)
    (fun i _ => hX i) h.2.2.2.2.2
  have hb : SumBudget f ((n.val^4:ℕ)*γ) := budget_mono he (fun _ => norm_nonneg _) (fun i =>
    le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg (add_nonneg ha h.2.1.le) (by positivity))))
  apply budget_mono (Product.set_products hb) (fun _ => norm_nonneg _)
  intro i; unfold valueP; split
  next hi => exact norm_prod_le ..
  next hi => rw [norm_zero]; exact prod_nonneg fun i _ => norm_nonneg _

/-- Calculation of the *actual* series on hard overlap graphs.
A sufficient hit threshold; no convergence assumption on either series.
R can also encode a previous tested stencil (so long as edges are still
payable by overlaps). Hard includes incompatibility of an address with
itself. -/
theorem price_log (hr : Hard R) {n : Side} (X : ι → Support n) (B : ℕ)
    (ht : Tests R X) {a γ δ q : ℝ} (ha : 0 ≤ a)
    (h : Ready X B (fun i => ‖w i‖) a γ δ q) :
    SumBudget (fun s => ‖valueP R w s‖) (Real.exp ((n.val^4:ℕ)*γ)) ∧
    SumBudget (fun i => ‖termP R w i‖) (((n.val^4:ℕ)*γ)*(1-q)⁻¹) ∧
    NormedSpace.exp (logS R w) = totalP R w := by
  have hX i : (X i).Nonempty := by obtain ⟨x,hx,-⟩ := ht i i (hr.diag i); exact ⟨x,hx⟩
  have hb := actual_values R w X B hX ha h
  have hB := absoluteS R w X B ht hX ha h
  suffices he : NormedSpace.exp (logS R w) = totalP R w from
    ⟨hb,hB,he⟩
  have he (D : Finset ι) : NormedSpace.exp (∑' i,boundTo R w D i)=∑' i,pickedFrom R w D i := by
    let x i := X (i:↥D).val
    rw [actual,literal]; refine finite_log (γ:=γ) (δ:=δ) (q:=q) (chosenRel R D) _ ⟨fun i => hr.diag _,fun i j => hr.symm _ _⟩
      x B (fun i j => ht _ _) (fun i => hX _) ha ?_
    obtain ⟨hg,hd,hq,hn,hw,hh⟩ := h
    refine ⟨hg,hd,hq,hn,fun _ => norm_nonneg _,fun y => ?_⟩
    have hv := budget_pull (fun j : ↥D => j.val) Subtype.val_injective (hh y)
    exact hv
  have hf : Tendsto (fun D => ∑' i,boundTo R w D i) atTop (𝓝 (logS R w)) := by
    apply tendsto_tsum_of_dominated_convergence hB.2.1
    · intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (univ.image i.2)] with D hD
      exact (show boundTo R w D i = _ from if_pos (fun j => hD (mem_image_of_mem _ (mem_univ j)))).symm
    refine Eventually.of_forall fun D i => ?_
    unfold boundTo; split <;> first | exact le_rfl | exact norm_zero.trans_le (norm_nonneg _)
  have hg : Tendsto (fun D => ∑' i,pickedFrom R w D i) atTop (𝓝 (totalP R w)) := by
    apply tendsto_tsum_of_dominated_convergence hb.2.1
    · intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop i] with D hD
      exact (show pickedFrom R w D i = _ from if_pos hD).symm
    refine Eventually.of_forall fun D i => ?_
    unfold pickedFrom; split <;> first | exact le_rfl | exact norm_zero.trans_le (norm_nonneg _)
  exact tendsto_nhds_unique ((NormedSpace.exp_continuous.continuousAt.tendsto.comp hf).congr he) hg
end YM.QCD.GasP
