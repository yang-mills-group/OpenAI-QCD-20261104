import YM.Fir.Kilt
import YM.Fir.Bound
/-! Finite-dimensional tensor jet bounds from the calibrated prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Analysis YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric TagF Sash
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open Finset
open scoped Topology ContDiff BigOperators Classical
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
variable {Z:SpaceZ}(H:Ability P φ Z) {M:∀ d:ℕ,Axis→Label d→ₗ[ℂ] Label (d+2)}
namespace Gains
variable (h:Gains M Z)
noncomputable def riot (n:ℕ): Module.Basis (FrameI n) ℝ (Points n):= (Pi.basisFun ℝ (FrameI n)).map (crossing n).toLinearEquiv.symm
lemma amber (b:FrameI n): riot n b=Points.direction b.1 b.2:=by apply (crossing n).injective; rw[pivotF]; unfold riot; simp
-- next
local instance choir (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance -- included h? issue
include h
lemma lenses (t:Fin n→TagF)(j:ℕ)(B:Fin j→FrameI n): ∃ p:Fin n→TagF,∀ x∈conf n, iteratedFDeriv ℝ j (handle Z t) x (riot n ∘ B) = handle Z p x:=by
    induction j generalizing t with
    | zero=> exact ⟨t,fun x _=> iteratedFDeriv_zero_apply ..⟩
    | succ j ih=>
      let p:= turnsH M t (B 0); obtain ⟨q,hq⟩:= ih p (Fin.tail B); refine ⟨q,fun x hx=>?_⟩
      have hP:= ((h.smooth t).of_le (show ((j+1:ℕ): WithTop ℕ∞)≤ ∞ from (by exact_mod_cast (show ((j+1:ℕ): ℕ∞) ≤ ⊤ from le_top)) )).contDiffAt ((conf_open n).mem_nhds hx); rw [← Fin.cons_self_tail (riot n ∘ B),cons_inner hP]
      have hp : D ((riot n ∘B) 0) (handle Z t) =ᶠ[𝓝 x] handle Z p:=by unfold Function.comp; rw [amber]; exact (show ∀ᶠ y in 𝓝 x,y∈conf n from (conf_open n).mem_nhds hx).mono (fun y hy=> h.openD y hy t _ _) -- mono.binder
      rw[(hp.iteratedFDeriv ℝ j).eq_of_nhds]; exact hq x hx
omit h
noncomputable def spurH(n:ℕ)(i:FrameI n): Points n →L[ℝ]ℝ:= ((riot n).coord i).toContinuousLinearMap
set_option quotPrecheck false
local notation "Zp"=> Points n
lemma windsor {j:ℕ} (T' : ContinuousMultilinearMap ℝ (fun _ : Fin j=>Points n) ℂ)(B: (Fin j→FrameI n)→ℝ)(hB:∀ i: Fin j→ FrameI n, ‖T' (riot n ∘i)‖ ≤ B i): ‖T'‖ ≤ ∑ i:Fin j→FrameI n,(∏ a:Fin j, ‖spurH n (i a)‖)*B i:=by
    let I:=Fin j→ FrameI n; let Q(i:I):= riot n ∘ i; let L(i:I):=∏ a:Fin j, ‖spurH n (i a)‖; have hx(i:I):0 ≤ L i:=Finset.prod_nonneg fun i _=> norm_nonneg _
    refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun i _=> mul_nonneg (hx i) ((norm_nonneg _).trans (hB i))) (fun u=>?_) -- arg
    have hz:T' u=∑ i:I,(∏ a, spurH n (i a) (u a)) • T' (Q i):=by
        have h(a):∑ c:FrameI n, spurH n c (u a) • riot n c=u a:=(riot n).sum_repr (u a)
        have hq:= MultilinearMap.map_sum T'.toMultilinearMap (α:=fun _=>FrameI n) (fun i b=> spurH n b (u i) • riot n b); conv_lhs=> rw [← funext h]
        exact hq.trans (Finset.sum_congr rfl fun i _=> T'.toMultilinearMap.map_smul_univ _ _)
    rw [hz]; apply (norm_sum_le ..).trans; rw [sum_mul]; refine Finset.sum_le_sum (fun i _=> ?_); rw [norm_smul,norm_prod]; have hv:0 ≤ B i:= (norm_nonneg _).trans (hB i); have ht(i:I): 0 ≤ L i *∏ a,‖u a‖:=mul_nonneg (hx i) (prod_nonneg fun _ _=> norm_nonneg _); refine (mul_le_mul ?_ (hB _) (norm_nonneg _) (ht i)).trans_eq (by unfold L; ring); unfold L; rw [←prod_mul_distrib]; exact prod_le_prod (fun _ _=> norm_nonneg _) fun a _=> (spurH n _).le_opNorm _
include h hp hr hφ H G
lemma temper (t:Fin n→TagF)(j:ℕ):∃ m:ℕ,∃ A:ℝ,0 ≤ A ∧ ∀ r:ℝ,0 < r → r ≤ 1 →∀ x:Points n, spaced r x → ‖iteratedFDeriv ℝ j (handle Z t) x‖ ≤ A*r⁻¹^m:=by
    let I:= Fin j→FrameI n; choose t' ht using lenses h t j
    choose μ F hF hM using fun i:I=> expanse hp hr (fun a=>(t' i a).1) hφ H (G:=G) (fun a=>(t' i a).2)
    let m:=∑ i:I, μ i; let L(i:I):ℝ:=∏ a:Fin j, ‖spurH n (i a)‖; have hq(i:I):0 ≤ L i:=prod_nonneg fun _ _=> norm_nonneg _
    refine ⟨m,∑ i:I,L i*F i,sum_nonneg fun i _=> mul_nonneg (hq _) (hF _),fun r he hh x hv=>?_ ⟩; rw [sum_mul]; let T (i:I):= F i*r⁻¹^m; refine (windsor _ T (fun i=>?_ )).trans_eq (sum_congr rfl fun i _=>by unfold T L; ring)
    rw [ht i x (spaced_conf he hv)]; exact (hM i r he hh x hv).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_inv₀ he|>.mpr hh) (single_le_sum (fun _ _=> Nat.zero_le _) (mem_univ _))) (hF _))
end Gains
end YM.Massive.Fir
#print axioms YM.Massive.Fir.Gains.temper
