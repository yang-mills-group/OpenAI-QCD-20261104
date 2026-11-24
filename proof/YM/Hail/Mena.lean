import YM.Hail.Dyke
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
open StressFlux (pair pairDeriv curl0 curl1)
-- scalar insertion at either. Maxwell glide kills. objective ray on these.
open Massive.Tawny Massive.Tawny.Cast Massive.Tawny.Cast.Perla Massive.Tawny.Cast.Perla.Fore Massive.Tawny.Cast.TableT
open Massive.Patria.Gall.Seals
open scoped BigOperators ContDiff
open Finset
local notation "S"=> RawTensor 1 8
variable {d:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2)
local notation "V"=> dual 10 d x
noncomputable def gale (t:S) : Axis→ Pol d →ₗ[ℂ] ℂ:=fun a=>∑ k:Axis,rayL k x hx 8 d (t.val (k,a)).val
lemma gale_at : gale (d:=d) x hx epi= 0:=by funext m; unfold gale; change (∑ k:Axis, _)=0; apply Finset.sum_eq_zero; intro k _; rw[epi_at]; split; exact emptyD k x hx; exact map_zero _
lemma wisp : ∑ k:Axis,∑ m:Axis, GE k m k a m=(1/2:ℂ) • lunar.val a:=by
   apply Subtype.ext; change (∑ k:Axis,∑ m:Axis, _ : Label 10).val= _; rw [show lunar.val a=∑ i:Axis,∑ j:Axis,GE i j a i j from rfl]; simp only[AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul]; 
   change (∑ k:Axis,∑ m:Axis, plain 10 (StressFlux.pairDeriv su k m k a m).val)= (1/2:ℂ) • ∑ i:Axis,∑ j:Axis, plain 10 (StressFlux.pairDeriv su i j a i j).val; simp_rw [← _root_.map_sum]; rw [← map_smul]; apply congr_arg; apply Labels.eval_ext; intro J; have h:=rosy (J 0) (J 1) a; rw [plotH] at h; simp only[Patria.Gall.leanV0,Patria.Gall.leanV1,Patria.Gall.Seals.pole] at h; simp_rw [_root_.map_sum,map_smul,_root_.map_sum,StressFlux.pairDeriv_value]; exact h
lemma spire_D : gale (d:=d) x hx spire a = (1/2:ℂ) • V (lunar.val a).val + V (eulerV.val a).val:=by
   change (∑ k:Axis, _)=_; simp_rw [spire_val, AddSubmonoidClass.coe_finsetSum,map_sum]; simp_rw [show ∀ i l k m j,rayL j x hx 8 d (GG i l k m).val= V (GE i l j k m).val + V (GE k m j i l).val from (fun i l k m j=> pair_Diff ..),sum_add_distrib]; rw[show (∑ k:Axis,∑ m:Axis,V (GE k m k a m).val)=(1/2:ℂ) • V (lunar.val a).val from ?_,Finset.sum_comm (f:=fun i l=>V (GE a l i i l).val), show (∑ i:Axis,∑ l:Axis,V (GE a i l l i).val)=V (eulerV.val a).val from ?_]
   swap; · rw[← map_smul,←Submodule.coe_smul, ← wisp]; simp only[AddSubmonoidClass.coe_finsetSum,map_sum]
   rw [show eulerV.val a= (∑ i:Axis,∑ l:Axis,GE a i l l i) from rfl]; simp only[AddSubmonoidClass.coe_finsetSum,map_sum]

lemma darkD : gale (d:=d) x hx eclipse a=(2:ℂ) • V (lunar.val a).val:=by
    unfold gale; simp_rw [dark]; rw[sum_eq_single a (?_) (by simp)]; rw [if_pos (Eq.refl a)]; rw [show lunar.val a= (∑ i:Axis,∑ l:Axis,GE i l a i l) from rfl]; simp only [AddSubmonoidClass.coe_finsetSum,map_sum, two_smul]; simp_rw [show ∀ i l,rayL a x hx 8 d (GG i l i l).val= V (GE i l a i l).val+V (GE i l a i l).val from fun i l=>pair_Diff ..,sum_add_distrib]
    intro b _ h; rw [if_neg h]; exact map_zero _
lemma haloD : gale (d:=d) x hx shadow a= (2:ℂ) • V (leapV.val a).val:=by
    unfold gale; simp_rw [shadow_val]; rw[sum_eq_single a (?_) (by simp)]; rw [if_pos (Eq.refl a)]; rw [show leapV.val a= (∑ i:Axis,GE a i a a i) from rfl]; simp only [AddSubmonoidClass.coe_finsetSum,map_sum, two_smul]; simp_rw [show ∀ i,rayL a x hx 8 d (GG a i a i).val= V (GE a i a a i).val+V (GE a i a a i).val from fun i=>pair_Diff ..,sum_add_distrib]
    intro b _ h; rw[if_neg h]; exact map_zero _
end YM.Hail
#print axioms YM.Hail.spire_D
#print axioms YM.Hail.darkD
