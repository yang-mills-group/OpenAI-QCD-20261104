import YM.Portland.Count
import YM.Massive.PCAC.Echo
import YM.QCD.Globe.Fife
/-! # second projection in E cost.Separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ovule
open Function Finset NormedSpace Creek
open scoped BigOperators Topology ContDiff Classical
variable {A I J:Type*}[Fintype A][Fintype I]
variable (i j:A)(x y:Alg A)
local notation "μ"=> core _
open Stew Grass.Ward
lemma rem_price (n:ℕ): priceD x n= ‖panel n x‖:=by unfold priceD; rw [Grass.norm_def]; simp_rw [angel,apply_ite Norm.norm,norm_zero,sum_filter] -- adjust
lemma respite (n:ℕ): bins A (x-panel n x) n=0:=by
    have h:= prices (x-panel n x) n; rw [rem_price] at h; rw [map_sub, past _ _ (chamber n x),if_pos rfl,sub_self,norm_zero,mul_zero] at h; exact le_antisymm h (r_nn ..)
lemma coup : μ (vary i (vary j x))= μ (vary i (vary j (panel 2 x))):=by
    apply sub_eq_zero.mp; rw [← map_sub, ← map_sub, ← map_sub]; apply norm_le_zero_iff.mp; let Y:=x-panel 2 x; exact le_trans (oneB i (vary j Y) 0) ((oneB j Y 1).trans (respite x 2|>.le))
section
open Massive Massive.PCAC
variable (X :Dirac A)(T:Sour A)(h:Stew.panel 2 X=form T)
include h
lemma readB : μ (vary (X:=Pairs A) (Sum.inl i) (vary (Sum.inr j) X))= -T j i:=by
    rw [coup,h,form_row,map_neg,map_sum,map_neg,map_sum, sum_eq_single i]; · rw [map_smul,vary_self,map_smul,map_one,smul_eq_mul,mul_one]; -- maybe defeq simp
    · intro j _ hj; rw [map_smul,show vary _ (psi j)=0 from vary_off _ _ (fun h=> hj (Sum.inl_injective h.symm)),smul_zero,map_zero]
    simp
lemma missB : μ (vary (X:=Pairs A) (Sum.inl i) (vary (Sum.inl j) X))=0:=by
      rw [coup,h]; unfold form; simp_rw [map_sum]; apply sum_eq_zero; intro x _; apply sum_eq_zero; intro y _; rw [map_smul,vary_mul,vary_off (X:=Pairs A) (Sum.inl j) (Sum.inr x) (by simp),mul_zero,add_zero]; by_cases he:j=y; · subst y; rw [vary_self,one_mul,map_smul,vary_off (X:=Pairs A) (Sum.inl i) (Sum.inr x) (by simp),smul_zero,map_zero]
      rw [vary_off (X:=Pairs A) (Sum.inl j) (Sum.inl y) (by simpa using he),zero_mul,smul_zero,map_zero,map_zero] -- rw psi abbrev
lemma missV : μ (vary (X:=Pairs A) (Sum.inr i) (vary (Sum.inr j) X))=0:=by
      rw [coup,h,form_row]; simp_rw [map_neg,map_sum,map_smul,psi]; simp only [vary_off (X:=Pairs A) (Sum.inr i) (Sum.inl _) (by simp),map_zero,smul_zero,Finset.sum_const_zero,neg_zero] -- hole rewrite
lemma readL : μ (vary (X:=Pairs A) (Sum.inr j) (vary (Sum.inl i) X))= T j i:=by
      rw [show vary (X:=Pairs A) (Sum.inr j) (vary (Sum.inl i) X)= -(vary (Sum.inl i) (vary (Sum.inr j) X)) from CliffordAlgebra.contractLeft_comm _ _ _,map_neg, readB i j _ _ h,neg_neg]
end
noncomputable def unitW (i:A)(a:A):ℂ:= if i=a then 1 else 0
lemma unitV : spr (unitW i) =vary i:=by ext1 X; simp [spr,unitW]
-- wavelength maps
noncomputable def tint (e:I ↪ A)(p:I→ℂ)(x:A):ℂ:=∑ i:I,p i*unitW (e i) x
lemma veil (e:I ↪ A)(p:I→ℂ) : spr (tint e p) x=∑ i:I,p i • vary (e i) x:=by
    rw [turns]; unfold tint; simp_rw [sum_smul]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_eq_single (e i)]<;> simp [unitW] <;> intros <;> (first | contradiction | grind)
lemma fieldV (e:I ↪ A)(p:I→ℂ)(hp:∀ i,‖p i‖≤1) : ∀ j:A,‖tint e p j‖≤1:=by
     intro x; unfold tint; by_cases he:x∈Set.range e; · obtain ⟨i,rfl⟩:=he; simpa [unitW,e.injective.eq_iff] using hp i
     simp_rw [show ∀ i,unitW (e i) x=0 from fun i=>if_neg (fun h=>he ⟨i,h⟩)]; simp
end YM.QCD.Grass.Ovule
#print axioms YM.QCD.Grass.Ovule.readB
#print axioms YM.QCD.Grass.Ovule.missV
