import YM.MassiveQCD.Evolution.SnapK
import YM.Push.ABSOLUTE_SUMS.Array
/-! # Joint uniform Cauchy costs (continuum factor)
 `χ` for soft supported index chooses all occupancy vectors at once. Write a per-flag
 exponent possible included on labels before consuming. Choose radii shrinking by evident factor to afford. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Analysis.Shelf
open Function Filter Topology Finset MeasureTheory Complex Set Metric
open RG Push.AbsoluteSums
open scoped BigOperators Classical
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A][CompleteSpace A]
variable {ι κ δ : Type*} [Nonempty κ]
private lemma maxima (f:κ→ℝ) (he:∀ i,0≤ f i)(h:BddAbove (Set.range f)):
    ∃ i:κ,∀ j, f j≤2*f i:=by
    let p:=Set.range f; by_cases hz:0 < sSup p
    · obtain ⟨_,⟨i,rfl⟩,hi⟩:= exists_lt_of_lt_csSup (range_nonempty f) (by exact half_lt_self hz); exact ⟨i,fun j=> (le_csSup h (mem_range_self j)).trans (by linarith)⟩
    let i:κ:=Classical.arbitrary _; exact ⟨i,fun j=> (le_csSup h (mem_range_self j)).trans ((le_of_not_gt hz).trans (by linarith [he i]))⟩
lemma collection (u v:ℝ)(hh:0≤u)(hν:0≤v)(ht:v≤1/4)(Y:ι→κ→ℂ→A)(p:δ→ι→ℝ)(hp:∀ i x,0≤p x i)(hs:∀ i j,Roof (Y i j))(hx: ∀ i, ∃ x,0<p x i) (h: ∀ z∈sphere (0:ℂ) (1/2:ℝ),∀ (F:ι→κ)(x:δ),
       SumBudget (fun i=>p x i * ‖Y i (F i) z‖) u):
    ∃ B:ι×ℕ→ℝ, (∀ x:δ,SumBudget (fun (i:ι×ℕ)=>p x i.1 * B i) (4*u)) ∧ ∀ i j V, ‖(v:ℂ)^j • ampK (Y i V) j‖≤ B (i,j):=by
    let Q i j V:= ‖ampK (Y i V) j‖
    have hp' (f:ι→κ)(j:ℕ)(x:δ) : SumBudget (fun i=> p x i * Q i j (f i)) (u*2^j):=budget_of_sum (fun i=>mul_nonneg (hp _ _) (norm_nonneg _)) fun s=> protectedBudget (fun i=>Y i (f i)) (p x) s (fun i _=>hs i (f i)) (fun i=> hp _ _) j u (fun _ hh=>budget_sum (h _ hh f x) s)
    choose f hf using fun i j=> maxima (Q i j) (fun _=> norm_nonneg _) (by
       obtain ⟨x,hx⟩:= hx i
       refine ⟨u*2^j /p x i,?_⟩
       intro y hy; obtain ⟨v',rfl⟩:= hy; apply (le_div_iff₀ hx).mpr; rw [mul_comm]; exact budget_single (hp' (fun _=>v') j x) i)
    let B (i:ι×ℕ):= (1/4:ℝ)^i.2*2*Q i.1 i.2 (f i.1 i.2)
    refine ⟨B,fun x=>?_,fun i j V=> ?_⟩
    · let L (i:ℕ×ι):=p x i.2 * B (i.2,i.1); let s (k:ℕ):=2*u*(1/2:ℝ)^k
      have ht : SumBudget L (4*u):=budget_rows L s (fun k=>by
            convert budget_scale (by positivity : (0:ℝ) ≤ (1/4:ℝ)^k*2) (hp' (fun i=>f i k) k x) using 1
            · unfold L B; funext i; ring
            unfold s; rw [show (1/2:ℝ)= 1/4* (2:ℝ) by norm_num,mul_pow]
            ring_nf
         ) (budget_loosen (budget_geometric (show 0 ≤ 2*u from by positivity) (by norm_num : (0:ℝ)≤1/2) (by norm_num)) (by norm_num; linarith))
      exact budget_pull (@Prod.swap ι ℕ) (Equiv.prodComm ι ℕ).injective ht
    rw [norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hν]; exact (mul_le_mul (pow_le_pow_left₀ hν ht _) (hf i j V) (norm_nonneg _) (by positivity)).trans_eq (mul_assoc ..).symm
end YM.MassiveQCD.Analysis.Shelf
