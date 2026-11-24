import YM.QCD.Nola.Idea
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι κ A B:Type*} {n n': Side} {m u:ℕ} [Fintype A][Fintype B]{s t a χ δ v C H η b:ℝ}
open Kites Pads Creek.Ledge
variable (p:A→Site n)(q:B→Site n')
lemma viaduct_nn (x:Alg A)(U:Support n)(h:0<t): 0 ≤ viaduct p U x t m:=sum_nonneg fun i _=> mul_nonneg (by positivity) (zero_le_one.trans (tell_one ..))
lemma band_s (x:Alg A)(v:ℂ): band p (v • x) t m= ‖v‖ * band p x t m:=by unfold band grainH; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [map_smul,norm_smul]; ring
lemma band_m (s:Finset A):band p (mono s) t m=t^s.card * tell (edges p s) m:=by
     unfold band grainH; rw [sum_eq_single s];
     · simp
     · intro i _ h; simp [read_other _ _ h]
     simp
variable {p': A→Site n'} (M:Matrix A B ℂ)(z₀:Support n')
lemma cargo (x:A)(he:p' x∈z₀)(U:Alg B)(h:0<t)(hp:∑ j, ‖M x j‖ * rodM (p' x) (q j) m ≤ C): viaduct q z₀ (changeVars M (atom x) * U) t m ≤ C*t *viaduct q z₀ U t m:=by
     rw [change_atom,sum_mul]; let D:= viaduct q z₀ U t m; apply le_trans (arch_sum q z₀ h ..); apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp h.le) (viaduct_nn ..)); swap; -- check maybe arguments
     all_goals try assumption
     rw [sum_mul,sum_mul]; apply sum_le_sum; intro i _; rw [smul_mul_assoc, arch_s]; exact (mul_le_mul_of_nonneg_left (arch_up q z₀ i (p' x) he U h) (norm_nonneg _)).trans_eq (by ring)
lemma cargoS (S:Finset A)(he:edges p' S⊆ z₀)(h:0<t)(hh:0 ≤ C)(hp:∀ x,∑ j,‖M x j‖*rodM (p' x) (q j) m ≤ C): viaduct q z₀ (changeVars M (mono S)) t m ≤ (C*t)^S.card*tell z₀ m:=by
     induction S using Finset.induction_on with
     | empty=> rw [mono_empty,map_one,arch_one]; simp
     | insert a S ha ih=>
          have hx : viaduct q z₀ (changeVars M (mono {a}*mono S)) t m ≤ (C*t)^(S.card+1)*tell z₀ m:=by
              rw [mono_single,map_mul]; exact (cargo q M z₀ a (he (mem_image_of_mem _ (mem_insert_self ..))) _ h (hp a)).trans ((mul_le_mul_of_nonneg_left (ih ((image_subset_image (subset_insert ..)).trans he)) (mul_nonneg hh h.le)).trans_eq (by ring))
          obtain hp|hp:= mono_mul_sign {a} S (by simp [ha]) <;> rw [card_insert_of_notMem ha] <;> rw [hp,disjUnion_eq_union,singleton_union] at hx
          · exact hx
          rwa [map_neg,arch_n] at hx
lemma cargoX (X:Alg A)(hv:0<v)(ht:0<t)(hb:0 ≤ b)(hH:0≤H)(h:0≤C)(hk:C*v ≤ t*b)(hp:b≤1)(he:∀ x,∑ j, ‖M x j‖*rodM (p' x) (q j) m ≤ C)(hy:∀ S:Finset A,tell (edges p' S) m ≤ H*tell (edges p S) m)(hX:∀ j: Finset A,j.card<u→coef j X=0): band q (changeVars M X) v m ≤ b^u*H*band p X t m:=by
     conv_lhs=> rw [← write X,map_sum]
     refine le_trans (bandS q _ _ hv) ?_; unfold band; rw [mul_sum]; apply sum_le_sum; intro i _; rw [map_smul]
     by_cases hj:i.card<u
     · rw [hX i hj,zero_smul]; simp [grainH, hX _ hj]
     let U:= edges p' i
     change band q (coef i _ • changeVars _ _) v m ≤ _; rw [band_s]; apply (mul_le_mul_of_nonneg_left ((into q U _ hv).trans (cargoS q M U i (Finset.Subset.refl _) hv h he)) (norm_nonneg _)).trans ; unfold grainH; have h1:= pow_le_pow_left₀ (mul_nonneg h hv.le) hk i.card; rw [mul_pow t b] at h1; have h2 : b^i.card ≤ b^u:= pow_le_pow_of_le_one hb hp (le_of_not_gt hj) -- le_of_not_gt? not less
     apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (le_trans h1 (mul_le_mul_of_nonneg_left h2 (pow_nonneg ht.le _))) (hy i) (zero_le_one.trans (tell_one ..)) (mul_nonneg (pow_nonneg ht.le _) (pow_nonneg hb _))) (norm_nonneg _)); apply le_of_eq; ring
end YM.QCD.Nola
