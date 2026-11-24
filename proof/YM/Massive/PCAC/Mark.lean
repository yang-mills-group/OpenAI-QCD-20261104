import YM.QCD.Creek.Wake
import YM.QCD.Grass.SD
/-!
# Exact even Ward generators and Lap components for the blocked identity
Hole: not estimates.
Columns and rows are independent; same row convention used for test matrix W,
 so the row/bar generator uses W-transpose. `work/massread.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
-- support general embedding also used on single side of a cut
-- elementary generator $L_{ij}$ replacing slot i generator with j generator.
noncomputable def gen (i j:A) : Alg A→ₗ[ℂ]Alg A:= (LinearMap.mulLeft ℂ (atom j)).comp (vary i)
lemma gen_mult (i j:A)(x y:Alg A): gen i j (x*y) = gen i j x*y+x*gen i j y:=by
    change atom j * vary i (x*y)=atom j*vary i x*y+x*(atom j*vary i y); rw [vary_mul,mul_add,mul_assoc,←mul_assoc (atom j) (grade x), show atom j * grade x=x*atom j from (line_across _ (grade x)).trans (by rw [grade_twice]; rfl),mul_assoc x]
lemma gen_atom (i j k:A): gen i j (atom k)=(if i=k then atom j else 0):=by
   change atom j * vary i (atom k)=_; split; · rename_i h; subst k; rw [vary_self,mul_one]
   rename_i h; rw [vary_off i k h,mul_zero]
lemma gen_integral (i j:Pairs A)(x:Dirac A): ber A (gen i j x)= (if i=j then ber A x else 0):=by
   have h:= integration (atom j*x) i
   rw [vary_head,map_sub,map_smul] at h; change ber A (atom j*vary i x) = _; rw [← sub_eq_zero.mp h]; by_cases h:i=j
   · subst i; simp [probe]
   simp [probe,h]
lemma gen_one (i j:A) : gen i j (1:Alg A)=0:=by change atom j*vary i 1=0; rw [vary_one,mul_zero]

abbrev Sour (A: Type*):= Matrix A A ℂ
/-- Even. `bar_j↦∑_i W i j bar_i` if `k=true`, else column action. -/
noncomputable def applyMark (k:Bool)(W:Sour A): Dirac A→ₗ[ℂ]Dirac A:= ∑ i:A,∑ j:A,W i j • (if k then gen (A:=Pairs A) (.inr j) (.inr i) else gen (A:=Pairs A) (.inl i) (.inl j))
lemma column (W:Sour A)(x: Dirac A): applyMark false W x = ∑ i:A,∑ j:A,W i j • gen (Sum.inl i) (Sum.inl j) x:=by simp [applyMark]
lemma row (W:Sour A)(x:Dirac A): applyMark true W x=∑ i:A,∑ j:A,W i j • gen (Sum.inr j) (Sum.inr i) x:=by simp [applyMark]
lemma leftP (W:Sour A)(i:A): applyMark false W (psi i)=∑ j:A,W i j • psi j:=by rw [column]; simp_rw [psi,gen_atom]; simp -- if j i l defeq
lemma leftB (W:Sour A)(i:A): applyMark true W (bar i)=∑ j:A,W j i • bar j:=by rw [row]; simp_rw [bar,gen_atom]; simp
lemma passP(W:Sour A)(i:A): applyMark true W (psi i)=0:=by rw [row]; simp [psi,gen_atom]
lemma passB(W:Sour A)(i:A): applyMark false W (bar i)=0:=by rw [column]; simp [bar,gen_atom]
lemma LMark (k: Bool)(W:Sour A)(x y: Dirac A): applyMark k W (x*y)= applyMark k W x*y+x*applyMark k W y:=by
   cases k <;> first | simp only [column,gen_mult,smul_add, sum_add_distrib,sum_mul, mul_sum,smul_mul_assoc, mul_smul_comm] | skip -- simp never fails
   simp only [row,gen_mult,smul_add,sum_add_distrib,sum_mul,mul_sum,smul_mul_assoc,mul_smul_comm]
lemma integrated(k:Bool)(W:Sour A)(x:Dirac A): ber A (applyMark k W x)= W.trace * ber A x:=by
   cases k <;> simp [applyMark, gen_integral, Matrix.trace, sum_mul] -- equality swapped

/-- Always in order `dψ_i` acting last, so acts on degree-two ψ bar with minus. -/
noncomputable def pairD (i j:A) : Dirac A→ₗ[ℂ]Dirac A:= (vary (X:=Pairs A) (Sum.inl i)).comp (vary (Sum.inr j))
noncomputable def lap (V:Sour A): Dirac A→ₗ[ℂ]Dirac A:= ∑ i:A,∑ j:A,V i j • pairD i j
lemma lap_apply (V:Sour A)(x:Dirac A): lap V x=∑ i:A,∑ j:A, V i j • vary (.inl i) (vary (.inr j) x):=by simp [lap,pairD]
lemma clearLap (V:Sour A)(x:Dirac A): ber A (lap V x)=0:=by rw [lap_apply]; simp only [map_sum,map_smul,integration,smul_zero,sum_const_zero]
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.integrated
