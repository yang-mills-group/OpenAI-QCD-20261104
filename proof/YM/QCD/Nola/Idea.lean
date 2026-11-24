import YM.QCD.Nola.Stall
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι κ A B:Type*} {n : Side} {m:ℕ} [Fintype A]{s t a χ δ v C H η b:ℝ}
open Kites Pads Creek.Ledge
variable (p:A→Site n)(s₀:Support n)
abbrev rodM (i j:Site n)(m:ℕ):= tell ({i,j}:Support n) m
lemma pairR (i j:Site n): reel ({i,j}:Support n)=separation i j:=by unfold reel; simp only [sup_insert,sup_singleton,separation_self, Nat.bot_eq_zero]; rw [separation_comm j i]; simp
lemma pairTell (i j:Site n):rodM i j m=(separation i j+1:ℝ)^m:=by rw [rodM,tell,pairR]
def viaduct (x:Alg A)(t:ℝ)(m:ℕ):ℝ:= ∑ i : Finset A, ‖coef i x‖ *t^i.card*tell (edges p i∪s₀) m
lemma into (x:Alg A)(h:0<t): band p x t m ≤ viaduct p s₀ x t m:=by apply sum_le_sum; intro i _; unfold grainH tell; gcongr; apply reel_mono; apply subset_union_left
lemma arch0 (h:Alg A): viaduct p s₀ (0:Alg A) t m=0:=by simp [viaduct]
lemma arch_add (hx:0<t)(x y:Alg A):viaduct p s₀ (x+y) t m≤ viaduct p s₀ x t m+ viaduct p s₀ y t m:=by unfold viaduct; rw [← sum_add_distrib]; refine sum_le_sum fun i _=>?_ ; rw [map_add,← add_mul, ← add_mul]; gcongr; exacts [zero_le_one.trans (tell_one ..),norm_add_le ..]
lemma arch_s (u:ℂ)(x:Alg A):viaduct p s₀ (u • x) t m=‖u‖*viaduct p s₀ x t m:=by unfold viaduct; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [map_smul,norm_smul]; ring
lemma arch_n (x:Alg A): viaduct p s₀ (-x) t m=viaduct p s₀ x t m:=by simp [viaduct]
lemma arch_sum (h:0<t)(f:ι→ Alg A)(s:Finset ι): viaduct p s₀ (∑ i∈s,f i) t m≤∑ i∈s, viaduct p s₀ (f i) t m:=by
   induction s using Finset.induction_on with
   | empty=>rw [sum_empty,sum_empty,arch0 p s₀ 0]
   | insert a s hh ih=> rw [sum_insert hh,sum_insert hh]; exact (arch_add p s₀ h ..).trans (add_le_add_right ih _)
lemma arch_mono (x:Finset A): viaduct p s₀ (mono x) t m = t^x.card * tell (edges p x∪s₀) m:=by
   unfold viaduct; rw [sum_eq_single x];
   · simp [Grass.read]
   · intro i _ h; simp [read_other _ _ h]
   simp
lemma arch_one : viaduct p s₀ (1:Alg A) t m= tell s₀ m:=by rw [← mono_empty,arch_mono]; simp [edges]
lemma arch_leg (x:A)(i:Site n)(he:i∈ s₀)(U:Finset A)(ht:0<t): viaduct p s₀ (atom x*mono U) t m ≤ (rodM i (p x) m * t)* viaduct p s₀ (mono U) t m:=by
    rw [← mono_single x,arch_mono]; by_cases h:x∈U
    · rw [mono_mul_zero _ _ (by simp [h]),arch0 p s₀ 0]; exact mul_nonneg (mul_nonneg (zero_le_one.trans (tell_one ..)) ht.le) (mul_nonneg (pow_nonneg ht.le _) (zero_le_one.trans (tell_one ..)))
    have hu: Disjoint {x} U:=by simp [h]
    have hh:= mono_mul_sign {x} U hu; let s:= insert x U
    have hv: tell (edges p s∪ s₀) m ≤ rodM i (p x) m * tell (edges p U∪s₀) m:=by
          have hz: edges p s∪s₀= {i,p x}∪(edges p U∪s₀):=by
                unfold s edges; ext a; by_cases hp:i=a; · subst a; simp [he]
                simp [Ne.symm hp,or_assoc]
          rw [hz]; exact tell_union (mem_insert_self ..) (mem_union_right _ he) _
    have ht':0≤t^(U.card+1):=by positivity
    have hs: viaduct p s₀ (mono (insert x U)) t m≤ rodM i (p x) m*t*(t^U.card*tell (edges p U∪s₀) m):=by rw [arch_mono,card_insert_of_notMem h]; exact (mul_le_mul_of_nonneg_left hv ht').trans_eq (by ring)
    rw [disjUnion_eq_union,singleton_union] at hh; rcases hh with h|h
    · rw [h]; exact hs
    rw [h,arch_n]; exact hs
lemma arch_up (x:A)(i:Site n)(he:i∈s₀)(U:Alg A)(ht:0<t): viaduct p s₀ (atom x*U) t m ≤ (rodM i (p x) m*t)*viaduct p s₀ U t m:=by
     conv_lhs=> rw [← write U,mul_sum]
     apply (arch_sum p s₀ ht ..).trans; rw [viaduct,mul_sum]; apply sum_le_sum; intro j _; rw [mul_smul_comm,arch_s]; apply le_trans (mul_le_mul_of_nonneg_left (arch_leg p s₀ x i he j ht) (norm_nonneg _)); rw [arch_mono]; apply le_of_eq; ring
end YM.QCD.Nola
