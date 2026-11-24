import YM.Kwick.Victor
import YM.Roan.Wire
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
/-- origin ticket value, and normalized optics.
-/
noncomputable def cashR (K S:ℝ)(n i:ℕ) := K^(n-i)/S
lemma cash_κ (K S:ℝ)(hp:0<K)(hS:0<S)(n:ℕ):(∀ i:ℕ, 0 < cashR K S n i)∧ (∀ i:ℕ,i<n → cashR K S n i=K*cashR K S n (i+1))∧ cashR K S n n=1/S:=by
       refine ⟨fun i=>div_pos (pow_pos hp _) hS,?_,?_⟩
       · intro i hi; unfold cashR; rw[show n-i=(n-(i+1))+1 from by omega,pow_succ]; ring
       unfold cashR; simp
local notation "R'"=> Flavor 6→ℂ
noncomputable abbrev prismA : Z→ₗ[ℂ](Flavor 6→ℂ):= pay1∘ₗlookB
noncomputable abbrev prismB : Z→ₗ[ℂ](Flavor 6→ℂ):= pay2∘ₗ lookQ
noncomputable def signature (k:ℝ)(x:Z→ₗ[ℂ] (Flavor 6→ℂ)) : Z→ₗ[ℂ] (Flavor 6→ℂ):= (k:ℂ) • x
noncomputable def compass (y s:ℝ) : Z→ₗ[ℂ] (Flavor 6→ℂ):= signature (y*s^2) (prismA)
noncomputable def torque (y s:ℝ) : Z→ₗ[ℂ] (Flavor 6→ℂ):= signature (y*s^2) (axM 0)
noncomputable def point (t y s:ℝ): Z→ₗ[ℂ] (Flavor 6→ℂ):= signature (t*(y*s^2)) (prismB)
variable (K:ℕ→ℝ){t A:ℕ→ℝ}{S:ℕ→BudgetPoint}{p:ℕ→Z}{n:ℕ}
variable {k w t':ℝ} {X:Z}
lemma bank_p (t t1:ℝ) : compass k w X= prismA ((k:ℂ) • stack 0 t w X) ∧ torque k w X=(axM 0) ((k:ℂ) • stack 0 t w X):=by
      simp only [stack,map_smul,smul_smul]; rw [show prismA=axM 1 from baseA,(βread X).1,(βread X).2]; unfold compass torque signature; rw [show prismA=axM 1 from baseA]; simp only [LinearMap.smul_apply]; unfold bud; change ( (↑(k*w^2):ℂ) • _=(↑k * ↑(t^0*w^2):ℂ) • _)∧((↑(k*w^2):ℂ) • _=(↑k*↑(t^0*w^2):ℂ) • _); norm_num
lemma point_p : point k t' w X= (k:ℂ) • prismB ((t':ℂ) • stack 1 k w X)+prismB ((t':ℂ) • stack 2 k w X):=by
      rw [show ((↑k:ℂ) • _+_)=(↑t':ℂ) • pay2 ((↑k:ℂ) • lookQ (stack 1 k w X)+lookQ (stack 2 k w X)) from ?_,←predV, map_smul, smul_smul]; swap
      · simp only [prismB,map_add,smul_add,map_smul, LinearMap.comp_apply]; rw[smul_comm (k:ℂ)]
      unfold point signature bud; rw [LinearMap.smul_apply]; change ( (↑(k*(t'*w^2)):ℂ) •_ )=(↑t'* ↑(k^1 *w^2):ℂ) • (prismB X); congr 1; push_cast; ring
lemma oR_t (v t:ℝ)(hv:0<v)(ht:0<t)(x:Z) : compass (1/v^2) v x=prismA x∧ torque (1/v^2) v x=axM 0 x∧ (point t (1/(t*v^2)) v x)=prismB x∧ compass (1/(t*v^2)) v x= (↑(t⁻¹):ℂ) • prismA x∧ torque (1/(t*v^2)) v x= (↑(t⁻¹):ℂ) • axM 0 x:=by -- uses real smul via algebra chain. maybe switch ℂ
         unfold compass torque point signature; simp only [LinearMap.smul_apply]; have h1: (1/v^2)*v^2=1:=by field_simp
         have h2:t*(1/(t*v^2)*v^2)=1:=by field_simp
         have h3: (1/(t*v^2)*v^2)=t⁻¹:=by field_simp
         rw [h1,h2,h3]; simp only [Complex.ofReal_one,one_smul] <;> trivial
lemma T_compare(v t:ℝ)(hv:0<v)(ht:0<t)(x:Z): point t (1/v^2) v x= (t:ℂ) • prismB x:=by
       unfold point signature; rw[LinearMap.smul_apply,div_mul_cancel₀ _ (sq_pos_of_pos hv).ne',mul_one]
structure Signature (k D:ℝ):Prop where
      pos:1 ≤ k
      ng:1 ≤ D
      qual (x:Z)(t:ℝ)(h:∀ i,wages i x ≤ t):‖x‖≤k*t
      read1(x:Z):‖prismA x‖≤D*‖x‖
      read0(x:Z):‖(axM 0) x‖≤D*‖x‖
      read2(x:Z):‖prismB x‖≤D*‖x‖
lemma lodging :∃ K D:ℝ, Signature K D:=by
       obtain ⟨k,hp,h⟩:= scaleK0; let D:= max (‖(axM 0).toContinuousLinearMap‖) (max (‖prismA.toContinuousLinearMap‖) (‖prismB.toContinuousLinearMap‖)); let T:= max 1 D
       refine ⟨k,T,hp,le_max_left ..,h,fun x=>?_ ,fun x=>?_,fun x=>?_⟩; exact (prismA.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))) (norm_nonneg _)); exact ((axM 0).toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (norm_nonneg _)); exact (prismB.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))) (norm_nonneg _))
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.point_p
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.lodging
