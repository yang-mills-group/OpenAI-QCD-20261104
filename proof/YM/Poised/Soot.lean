import YM.Poised.Pipes
import YM.Planned.PRIMARY_INTEGRAL_295.Cedar
/-!
# Moving budgets allowing full jet of regular test. Norm actual weighted exterior. Uniformly in dimension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n:ℕ}{c:Side}
namespace Pipes
open Pointwise Set Cedar Ember Oval
variable [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup X][NormedSpace ℝ X]
lemma budgeted_app (n:ℕ){Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](K:E→X→L[ℝ]Y)(F:E→X) (c d:ℝ) (hk:Ember n K d)(hf: Ember n F c): Ember n (fun x=>K x (F x)) (2^n * d*c) :=by
   have hd:=hk.2.1; have hc:=hf.2.1
   obtain ⟨S,hS,ho,hm⟩:= _root_.mem_nhds_iff.mp ((hk.1.eventually (by simp)).and (hf.1.eventually (by simp)))
   refine ⟨hk.1.clm_apply hf.1,by positivity,fun i hi=>?_⟩
   have hz:=norm_iteratedFDerivWithin_clm_apply (show ContDiffOn ℝ (↑n) K S from fun v hv=> (hS hv).1.contDiffWithinAt) (show ContDiffOn ℝ (↑n) F S from fun v hv=>(hS hv).2.contDiffWithinAt) ho.uniqueDiffOn hm (Nat.cast_le.mpr hi)
   simp only [iteratedFDerivWithin_of_isOpen _ ho hm] at hz
   refine hz.trans (le_trans (Finset.sum_le_sum (g:=fun j=>(i.choose j : ℝ)*d*c) (fun j hj=> ?_)) ?_)
   · have he : j ≤ i:= Nat.le_of_lt_succ (mem_range.mp hj); exact mul_le_mul (mul_le_mul_of_nonneg_left (hk.2.2 j (he.trans hi)) (by positivity)) (hf.2.2 _ ((Nat.sub_le ..).trans hi)) (norm_nonneg _) (by positivity)
   rw [← Finset.sum_mul, ← Finset.sum_mul]; have he : (∑ j ∈ Finset.range (i+1),(i.choose j:ℝ))=2^i:=by simpa [show (1+1:ℝ)=2 by norm_num] using (add_pow (1:ℝ) 1 i).symm
   rw [he]; gcongr <;> norm_num
-- if Ember all inputs (incl linear map from av finite) then Op.Act
section Clm
variable {Y : Type}[NormedAddCommGroup Y][NormedSpace ℝ Y] {c:ℝ}[FiniteDimensional ℝ X]
lemma total_op (T:E→X→L[ℝ] Y) (h:∀ x:X,ContDiffAt ℝ (↑n:WithTop ℕ∞) (fun k=>T k x) 0): ContDiffAt ℝ (↑n) T 0 :=by
    let B:=Module.finBasis ℝ X; let L i:= (B.coord i).toContinuousLinearMap; let q(x:E)(i):= (L i).smulRight (T x (B i)); rw [show T=(fun x=>∑ i,q x i) from ?_]; swap
    · funext x; ext v; unfold q; rw [_root_.sum_apply]; simp_rw [ContinuousLinearMap.smulRight_apply,← map_smul,← map_sum]; exact congr_arg _ (B.sum_repr ..).symm
    apply ContDiffAt.sum; intro i _; unfold q; exact ((ContinuousLinearMap.smulRightL ℝ X Y (L i)).contDiff.contDiffAt).comp _ (h _)
lemma ticket (T:E→X→L[ℝ]Y) (hc:0≤c)(he:∀ i:X, Ember n (fun x=> T x i) (c*‖i‖)): Ember n T c:=by
    have hs:=total_op T (fun i=>(he i).1)
    refine ⟨hs,hc,fun j hj=>?_⟩
    let A:=iteratedFDeriv ℝ j T 0
    refine ContinuousMultilinearMap.opNorm_le_bound hc fun v=>ContinuousLinearMap.opNorm_le_bound (A v) (show 0 ≤ _* _ from mul_nonneg hc (prod_nonneg fun _ _=>norm_nonneg _)) fun x=>?_
    let L:=ContinuousLinearMap.apply ℝ Y x
    let F (s:E):=T s x
    rw [show A v x=iteratedFDeriv ℝ j F 0 v from (DFunLike.congr_fun (L.iteratedFDeriv_comp_left hs (Nat.cast_le.mpr hj)) v).symm]
    exact ((iteratedFDeriv ℝ j F 0).le_opNorm _).trans ((mul_le_mul_of_nonneg_right ((he x).2.2 j hj) (prod_nonneg fun _ _=>norm_nonneg _)).trans_eq (by ring))
lemma posted (T : X→L[ℝ]Y) (F:E→X) (h:Ember n F c){a:ℝ} (ht:‖T‖≤a): Ember n (T∘ F) (a*c):=by
    refine ⟨T.contDiff.contDiffAt.comp _ h.1,mul_nonneg ((norm_nonneg T).trans ht) h.2.1,fun i hi=>?_⟩; rw [T.iteratedFDeriv_comp_left h.1 (Nat.cast_le.mpr hi)]; exact (T.norm_compContinuousMultilinearMap_le _).trans (mul_le_mul ht (h.2.2 i hi) (norm_nonneg _) ((norm_nonneg _).trans ht)) -- name
end Clm
variable [Fintype A][Fintype B] [DecidableEq A]
open QCD.Stew
local notation "D"=> Alg A
local notation "W"=> Alg B
lemma tipped {Y:E→W}{C:ℝ}(h:Ember n Y C)(p:ℂ): Ember n (p • Y) (‖p‖*C):=by
    let L:W→L[ℝ]W:= p • ContinuousLinearMap.id ℝ W
    apply posted L _ _ _ -- defeq 
    · exact h
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
abbrev banner (T:A→B→ℂ)(n:ℕ) : D→L[ℝ]W:=(((changeVars T).toLinearMap.comp (panel n)).toContinuousLinearMap).restrictScalars ℝ
lemma about (T:E→A→B→ℂ)(C:ℝ)(ht: ∀ i:A, Ember n (fun x=>changeVars (T x) (atom i)) C)(v: List A): Ember n (fun t=> changeVars (T t) ((v.map atom).prod)) ((2^n*C)^v.length):=by
    induction v with
    | nil=> simp only [pow_zero, List.map_nil,List.prod_nil,List.length_nil,map_one]; simpa only [norm_one] using (Ember.constant (1:W) n (E:=E))
    | cons i v ih=>simp only [List.map_cons,List.prod_cons,map_mul,List.length_cons,pow_succ]; rw [mul_comm, mul_assoc]; exact Ember.fires (ht i) ih
lemma behaved (T:E→A→B→ℂ)(C:ℝ)(hC:0≤C)(ht: ∀ i:A, Ember n (fun x=>changeVars (T x) (atom i)) C): Ember n (fun t=>banner (T t) d) ((2^n*C)^d) :=by
    apply ticket _ (by positivity); intro A₁; let q:= (2^n*C)^d
    have hm(s:Finset A): Ember n (fun t=> banner (T t) d (mono s)) q:=by
       simp_rw [banner]; change Ember n (fun t=>changeVars (T t) (panel d (mono s))) q; simp_rw [past _ _ (Grass.homogeneous s)]; split
       next hv=> obtain ⟨V,hx,hy,H⟩:= expression s; rw [H]; apply (renamed (f:= fun t=> changeVars (T t) (((List.ofFn V).map atom).prod)) _ (EventuallyEq.of_eq ?_)); swap
                 · funext x; rw [List.map_ofFn]
                 have ht:= about T C ht (List.ofFn V); unfold q; rw [List.length_ofFn] at ht; rwa [hv]
       next h=> simp only [map_zero]; exact weakening (neutral n) (by unfold q; positivity)
    have hc (s:Finset A)(x:E): banner (T x) d (coef s A₁ • mono s)= coef s A₁ • banner (T x) d (mono s):=map_smul ((changeVars (T x)).toLinearMap.comp (panel d)) _ _ -- uses ℂ lin, not L
    rw [show (fun t=> banner (T t) d A₁)=(fun t=> ∑ s: Finset A,coef s A₁ • banner (T t) d (mono s)) from funext fun t=>by 
        conv_lhs=>arg 2; rw [← write A₁];
        simp_rw [map_sum,hc]] -- inspect
    exact weakening (total univ (fun i=>‖coef i A₁‖*q) _ (fun i _=> tipped (hm i) (coef i A₁))) (le_of_eq (by rw [← Finset.sum_mul, ← norm_def]; exact mul_comm ..)) -- namespace .weakening not works alias?
end Pipes
end YM.Massive.Poised
