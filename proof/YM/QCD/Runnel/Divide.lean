import YM.QCD.Runnel.Vote

/-! # transport from an adjacency graph, series -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Run
open Lat Lattice Gauge Wilson Cost Function Finset Kit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {f : Side} {D E F I : Type*} [Fintype D] [Fintype E] [Fintype F] [DecidableEq D] [DecidableEq E]
variable {x : D→Site f} {y : E→Site f} {z : F→Site f}
variable {δ b R R' S S' : ℝ} {B : ℕ}
variable {M N : Grid f → ArrayL D E} {K : Grid f → ArrayL E F}
namespace Heritage
lemma spanning (U : D → E → Support f) (X : D→E→Pulse f→Bundle) (m : D→E→ℝ)
    (h : ∀ i j,Crop (x i) (y j) δ (U i j) (X i j) (m i j)) (hp : ∀ i j P,X i j (settled P)=cell (M P) i j)
    (he : ∀ i, ∑ j,rent b B (U i j)*m i j ≤ R) (hf : ∀ j,∑ i,rent b B (U i j)*m i j≤R): Heritage x y δ b B M R:=by
  let P i j W:= if U i j=W then X i j else 0
  let Q i j W:= if U i j=W then m i j else 0
  have hm i j : duel Q i j b B=rent b B (U i j)*m i j:= by simp [duel,Q,mul_ite]
  refine ⟨P,Q,fun i j Z=> ?_,fun i j K=> ?_,fun i=> ?_,fun j=>?_⟩
  · unfold P Q; split_ifs with hv; · rw [← hv]; exact h i j
    exact Crop.zero
  · simp [P,ite_apply,hp]
  · simp_rw [hm]; exact he _
  simp_rw [hm]; exact hf _
lemma joined (L : Finset I) (T : I→Grid f→ArrayL D E) {W : I→ℝ} (h : ∀ i∈L, Heritage x y δ b B (T i) (W i)): Heritage x y δ b B (fun U=>∑ i∈L,T i U) (∑ i∈L,W i):=by
  classical
  induction L using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact vacant
  | insert a L ha ih=> simp_rw [sum_insert ha]; exact (h a (mem_insert_self ..)).plus (ih (fun i hi=>h i (mem_insert_of_mem hi)))
lemma heritage_one (x : D→Site f) (hd : 0≤b) : Heritage x x δ b B (fun _=>1) (Real.exp b):=by
  let U i (_:D) : Support f:={x i}
  let X i (j:D) (_:Pulse f):Bundle:= if i=j then 1 else 0
  let m (i j:D):ℝ := if i=j then 1 else 0
  have h i : coverNumber B ({x i}:Support f)≤1:=by
    have he : Corona.Ships {x i} (B+B+1):=by intro u hu v hv; simp only [mem_singleton] at hu hv; rw [hu,hv]
    exact (Corona.list_cost B (D:={x i}) ⟨halo_subset B _,Corona.ship_halo _ he⟩).trans (by rw [card_singleton])
  have hu i : rent b B ({x i} : Support f) ≤ Real.exp b := Real.exp_le_exp.mpr (mul_le_of_le_one_right hd (by exact_mod_cast h i))
  refine spanning U X m ?_ (fun i j P=> by rw [cell_one]) (fun i=> ?_) (fun i=>?_)
  · intro i j; by_cases hi:i=j
    · subst j; simp only [U,X,m,if_true]
      refine ⟨zero_le_one,fun _=>by simp, fun i _=> differentiableAt_const _,fun _ _=> one_bound,fun _ _ _=> rfl,fun P k=>?_⟩
      rw [mul_one]; exact (touch_u (x:=colour (k _)) ⟨su.mat_star_mul _,su.mat_mul_star _⟩).2.symm
    unfold X m; simp_rw [if_neg hi]; exact Crop.zero
  · simpa [U,m,mul_ite] using hu i
  simpa [U,m,mul_ite] using hu i
lemma power_pos {M : Grid f→ArrayL D D} (h : Heritage x x δ b B M R) (hd : 0<δ) (hp : 0≤b) (hr : 0≤R) (n : ℕ): Heritage x x δ b B (fun U=> M U^(n+1)) (R^(n+1)):=by
  induction n with
  | zero=> simpa using h
  | succ n ih=>
    simp_rw [pow_succ _ (n+1)]; exact ih.meet h hd hp (by positivity) hr
lemma power {M : Grid f→ArrayL D D} (h : Heritage x x δ b B M R) (hd : 0<δ) (hp : 0≤b) (hr : 0≤R) (n : ℕ): Heritage x x δ b B (fun U=> M U^n) (R^n * Real.exp b):=by
  cases n with
  | zero=> simpa only [pow_zero,one_mul] using heritage_one (B:=B) (δ:=δ) x hp
  | succ n=> exact (power_pos h hd hp hr n).mono (le_mul_of_one_le_right (by positivity) (Real.one_le_exp hp))
lemma cell_mon (i:D) (j:E) {M : I→ArrayL D E} {R} (h : HasSum M R) : HasSum (fun k=> cell (M k) i j) (cell R i j):= by
  let k : ArrayL D E →ₗ[ℂ] Bundle:= { toFun:= fun X=>cell X i j,map_add':=fun X Y=>rfl,map_smul':=fun X Y=>rfl }; exact k.toContinuousLinearMap.hasSum h
lemma congregation {T : I→Grid f→ArrayL D E} {p : I→ℝ} (hd : 0<δ) (hp : 0≤b) (h : ∀ i, Heritage x y δ b B (T i) (p i))
    (hm : Summable p) (he : ∀ U, HasSum (fun i=>T i U) (M U)): Heritage x y δ b B M (∑' i,p i):=by
  choose X Y H using h
  let W i j P:=∑' k, Y k i j P
  have hu i j P : Summable fun k=>Y k i j P:=by
    apply hm.of_nonneg_of_le (fun k=> ((H k).crop i j P).1)
    intro k; exact (le_mul_of_one_le_left ((H k).crop i j P).1 (market hp B P)).trans (payme (H k) i j P)
  have ht i j : duel W i j b B=∑' k,duel (Y k) i j b B:=by
    unfold duel W; rw [Summable.tsum_finsetSum]; apply sum_congr rfl; intro a _; rw [(hu i j a).tsum_mul_left]
    exact fun i' _ => (hu i j i').mul_left _
  have hw i j : Summable fun k=>duel (Y k) i j b B:= summable_sum fun a _=> (hu i j a).mul_left _
  refine ⟨fun i j P Z=>∑' k,X k i j P Z, W,fun i j P=> Crop.church _ (hu i j P) (fun k=>(H k).crop ..) hd,fun i j U=> ?_,fun i=>?_,fun j=>?_⟩
  · rw [← (cell_mon i j (he U)).tsum_eq]; simp_rw [fun k=> ((H k).sells i j U).symm]
    rw [Summable.tsum_finsetSum]; intro a _; exact (hu i j a).of_norm_bounded (fun k=> ((H k).crop i j a).2.2.2.1 _ (citizenship _ hd U))
  · simp_rw [ht]; rw [← Summable.tsum_finsetSum (f:=fun j k=>duel (Y k) i j b B) (fun j _=>hw i j)]; exact (summable_sum (fun j (_ : j∈univ)=> hw i j)).tsum_le_tsum (fun k=>(H k).spends i) hm
  simp_rw [ht]; rw [← Summable.tsum_finsetSum (f:=fun i k=>duel (Y k) i j b B) (fun i _=>hw i j)]; exact (summable_sum (fun i (_ : i∈univ)=> hw i j)).tsum_le_tsum (fun k=>(H k).dues j) hm
end Heritage
end YM.QCD.Run
