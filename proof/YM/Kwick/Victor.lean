import YM.Kwick.Sprig
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
variable (x y: Z)
lemma scaleK0 :∃ D:ℝ,1 ≤D ∧ ∀ (x:Z)(t:ℝ), (∀ j:Axis,wages j x ≤ t)→ ‖x‖≤ D*t:=by
     obtain ⟨K,hk,H⟩:= breathM 10; refine ⟨K,hk,fun x t ht=>?_⟩; change ‖x.val‖ ≤ _; have hx:0≤t:= (wageG ..).trans (ht 0); apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) hx)).mpr; intro a; refine (H (x.val a)).trans (mul_le_mul_of_nonneg_left (le_trans (?_) (ht a)) (by linarith))
     apply le_of_eq; apply Finset.sum_congr rfl; intro i _; rw [bLoom]; simp only [stitchQ,one_pow,mul_one,Complex.ofReal_one, one_mul]
lemma zeroJ : bet 0 x=0 ↔ axM 0 x=0 ∧ axM 1 x=0:=by
      constructor
      · intro h; have ht:= βread x; rw [h,map_zero,map_zero] at ht; exact ⟨ht.2.symm,ht.1.symm⟩
      obtain ⟨⟨u,c⟩,rfl⟩:= certified.2 x; rintro ⟨h,e⟩; have hp(i:Flavor 6):u i 0=0∧u i 1=0:=by
            suffices H:(bodyS (plaza (u,c))).1 i 0=0∧(bodyS (plaza (u,c))).1 i 1=0 by rw [bodyι] at H; exact H
            exact ⟨congr_fun h i,congr_fun e i⟩
      rw [lowly]; refine sum_eq_zero fun i _ =>?_ ; rw[(hp i).1,(hp i).2,zero_smul,zero_smul,add_zero]
lemma enough (k:Fin 4)(h:(tierQ k)=(8,0,2)):k=0:= (show Function.Injective tierQ by decide) h
lemma trustK(P: BudgetPoint)(w:ℝ)(h:0<w):Function.Injective (fun x:Z=> fun k: Fin 4=> Stair.stack k P.threshold w x):=by
      intro x y he; rw [bill_zero x,bill_zero y]; refine Finset.sum_congr rfl fun i _=>?_ ; exact smul_right_injective _ (show (bud i P.threshold w:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (mul_pos (pow_pos P.threshold_pos _) (pow_pos h _)).ne') (congr_fun he i)
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.scaleK0
