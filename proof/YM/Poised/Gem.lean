import YM.Poised.Comb
import YM.Poised.Merian
/-!
# E4 span in actual spin variables
ordinary weight-n position polynomials. No even-prestate requirement. Cover d twice-weight. Count debt EXACT.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {d a l k n:ℕ}
namespace Gem
variable {F : Type*}[NormedAddCommGroup F][NormedSpace ℝ F]
-- evaluate continuum position at seat
abbrev score (p:Multi d)(x:E4):ℝ:= ∏ i: Axis,(x i)^(power p i)/(Nat.factorial (power p i):ℝ)
def tags (B:Multi d→ F)(x:E4): F:= ∑ p: Multi d, score p x • B p
lemma homogeneous (p:Multi d) (v:F) : (fun x=>score p x • v) ∈exactDegree F (order (power p)):=by
   apply exact_of_smooth; swap
   · intro x t; unfold score order; rw [smul_smul];  simp_rw [PiLp.smul_apply,smul_eq_mul,mul_pow,mul_div_assoc, prod_mul_distrib,prod_pow_eq_pow_sum]
   unfold score; fun_prop
lemma tall (B:Multi d→F) (h:∀ p, n ≤ order (power p) → B p=0) : tags B ∈ rangeLt F n:=by
   rw [show tags B=∑ p:Multi d,fun x=>score p x • B p from funext fun x=>by rw [tags,Finset.sum_apply]]; apply Submodule.sum_mem; intro p _; by_cases hp:order (power p)< n; · exact exact_le_band hp (homogeneous ..)
   simp_rw [h p (le_of_not_gt hp),smul_zero]; exact Submodule.zero_mem _

private lemma wears (v : Fin n→Axis) (h:n≤d) : ∃ p:Multi d, order (power p)=n ∧ ∃ c:ℝ,∀ x:E4,(∏ i:Fin n,x (v i))=score p x*c:=by
   let m(j:Axis):=(∑ i:Fin n, if v i=j then 1 else 0:ℕ); have hm:order m=n:=by unfold order m; rw [sum_comm]; simp
   have hx i:m i ≤ d:= (Finset.single_le_sum (f:=m) (fun i _=>Nat.zero_le _) (Finset.mem_univ i)).trans ((show (∑ i,m i)=n from hm).le.trans h)
   let p:Multi d:=⟨fun i=> ⟨m i, Nat.lt_succ_of_le (hx i)⟩,hm.symm ▸ h⟩
   refine ⟨p,hm, ∏ i, (Nat.factorial (m i):ℝ),fun x=>?_⟩
   rw [score, ←prod_mul_distrib]; simp_rw [show ∀ i:Axis,power p i=m i from fun i=> rfl, show ∀ (i:Axis)(x:ℝ), x/(Nat.factorial (m i):ℝ)*Nat.factorial (m i)=x from fun i x=>div_mul_cancel₀ _ (by positivity)]; unfold m; simp_rw [←prod_pow_eq_pow_sum]; rw [Finset.prod_comm]; refine Finset.prod_congr rfl fun i _=>?_ ; rw [Finset.prod_eq_single (v i)]; all_goals simp [eq_comm] <;> tauto
private lemma resonance (x:E4): (∑ i:Axis, x i • basis i)=x:=by ext i; simp
lemma goad {f:E4→F}(h:f∈exactDegree F n) (hn:n ≤ d) :∃ B:Multi d→F, tags B=f ∧ ∀ p, order (power p) ≠ n → B p=0:=by
   obtain ⟨A,rfl⟩:=can_write.mp h; choose p hp W h using fun (v:Fin n→Axis)=> wears v hn
   let B(v:Fin n→Axis):Multi d→ F:= Pi.single (p v) (W v • A (basis∘v))
   refine ⟨∑ v,B v,?_,fun i hi=>?_⟩
   · funext x; unfold Tensor.diagonal; unfold tags
     simp_rw [Finset.sum_apply, smul_sum]; rw [Finset.sum_comm]
     conv_rhs=> arg 2; ext i; rw [← resonance x] -- ext choices
     rw [A.map_sum (fun _ i=> x i • basis i)]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.sum_eq_single (p i)]
     · unfold B; rw [Pi.single_eq_same,A.map_smul_univ,h i x, smul_smul]; rfl
     · intro j _ hj; unfold B; rw [Pi.single_eq_of_ne hj,smul_zero]
     simp
   rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun j _=> Pi.single_eq_of_ne (fun he:i=p j=> hi (he.symm ▸ hp _)) _
lemma served {f:E4→F} (h:f∈rangeLt F n)(hn:n≤d+1) : ∃ B: Multi d→F,tags B=f ∧ ∀ p,n ≤ order (power p) → B p=0:=by
   obtain ⟨P,hP,rfl⟩:=range_decompose h; choose B hB hp using fun i=> goad (f:=P i) (hP i) (Nat.le_of_lt_succ (i.isLt.trans_le hn)) -- arg f
   refine ⟨∑ i,B i,?_,fun p h=>?_⟩
   · funext x; unfold tags; rw [Finset.sum_apply]; simp_rw [Finset.sum_apply,smul_sum]; rw [sum_comm]; exact Finset.sum_congr rfl fun j _=> congr_fun (hB j) x
   rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=> hp i p ((lt_of_lt_of_le i.isLt h).ne.symm)
end Gem
end YM.Massive.Poised
