import YM.Bloom.Lease
import YM.Hypnos.Berries
/-! # Tensor pricing unboosted. Without inst Loom problem. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom.TreeP
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit
open AnalyticBridge.LocalGaussianLaws.Current FreeResolvent
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G: Gauge}{c f:Side}{k m n j b q r:ℕ}{X Y Z:Type}
noncomputable def lavish (c:Side)(i:G.ColorIndex)(r:ℕ)(W:Matrix Unit (Co c (TypeFace r)) ℝ) : Matrix Unit (FreeResolvent.Slot G c r) ℂ:= of fun _ j=> if i=j.2.2 then (W () (j.1,j.2.1):ℂ) else 0
variable (V:Matrix (Co c (TypeFace k)) (Co f (TypeFace m)) ℝ)(x:G.ColorIndex)(P:Matrix Unit (Co c (TypeFace k)) ℝ)(y:G.ColorIndex)(Q:Matrix Unit (Co f (TypeFace m)) ℝ)
noncomputable def paid (G:Gauge){c f:Side}{k m:ℕ}(V:Matrix (Exterior.Body k c) (Exterior.Body m f) ℝ):= (FreeResolvent.tensor G V).map Complex.ofReal
lemma churn : lavish c x k P*paid G V=lavish f x m (P*V):=by
    ext ⟨⟩ ⟨i,a,b⟩; by_cases he:x=b
    · subst b; simp only [Matrix.mul_apply,Fintype.sum_prod_type,lavish,of_apply,ite_mul,zero_mul,sum_ite_eq,mem_univ,if_true,Complex.ofReal_sum,Complex.ofReal_mul,paid,Matrix.map_apply,FreeResolvent.tensor]
    rw [show lavish f x m (P*V) _ (i,a,b)=0 from if_neg he, Matrix.mul_apply]; refine sum_eq_zero fun k _=>?_ ; unfold lavish paid FreeResolvent.tensor; simp only [Matrix.map_apply, Matrix.of_apply]; split_ifs with hw ha hb <;> simp_all
lemma coversU : (lavish c x k P*paid G V*(lavish f y m Q).transpose) () ()= if x=y then ((P*V*Q.transpose) () ():ℂ) else 0:=by
    rw [churn,Matrix.mul_apply,Fintype.sum_prod_type]; by_cases h:x=y
    · subst y; rw [if_pos rfl,Matrix.mul_apply,Fintype.sum_prod_type]; apply Eq.trans _ (Complex.ofReal_sum ..).symm; apply sum_congr rfl; intro p _; simp_rw [Fintype.sum_prod_type,lavish, transpose_apply, Matrix.of_apply]; rw [Complex.ofReal_sum]; apply sum_congr rfl; intro i _; simp [ite_mul,mul_ite,Complex.ofReal_mul] -- syntax
    rw [if_neg h]; refine sum_eq_zero fun k _=> sum_eq_zero fun i _=>?_ ; unfold lavish; rw [transpose_apply]; simp only [of_apply]; split_ifs <;> simp_all
-- curvature jet lift EMP.True native flatten. use form kernel
open Next.SectorChange
variable (U:Directions G c)
noncomputable def boll (c:Side)(U:Directions G c): Matrix (FreeResolvent.Slot G c 1) Unit ℂ:=Matrix.of fun i _=> (FreeResolvent.flatten (Flat.labels U) i:ℂ)
noncomputable abbrev radi (G:Gauge)(c:Side): Matrix (FreeResolvent.Slot G c 2) (FreeResolvent.Slot G c 1) ℂ:= paid G (d 1 c)
lemma radial (ξ:ℝ) : (Matrix.of fun (i:FreeResolvent.Slot G c 2) (_:Unit) => ((ξ*Hypnos.Fruit.jet U i:ℝ):ℂ))=(ξ:ℂ) • (radi G c*boll c U):=by
    ext ⟨z,e,b⟩ ⟨⟩; rw [of_apply,Complex.ofReal_mul, Matrix.smul_apply,smul_eq_mul]; congr 1
    have he := congr_fun (FreeResolvent.component_mul (d 1 c) (FreeResolvent.flatten (Flat.labels U)) b) (z,e); change (↑(jet U (z,e,b)):ℂ)=_; rw [show jet U (z,e,b)= ((tensor G (d 1 c))*ᵥ (FreeResolvent.flatten (Flat.labels U))) (z,e,b) from Eq.symm he]; simp only [radi,paid,boll, Matrix.mul_apply,mulVec, dotProduct,Complex.ofReal_sum, Complex.ofReal_mul, Matrix.map_apply,Matrix.of_apply]
lemma vector_rate (i:FreeResolvent.Slot G c 1) : ‖boll c U i ()‖ ≤ ‖U‖:=by
    let w:=i.1; let v:=i.2.1; let s:=i.2.2; rw [boll, of_apply,Complex.norm_real]; change ‖U (w,axisEquiv.symm v) s‖ ≤ ‖U‖; exact (PiLp.norm_apply_le _ _).trans (norm_le_pi_norm U _)
-- row sizes.X
section sum
variable [Fintype Y][Fintype Z]
noncomputable def cusp (P:Matrix X Y ℂ) (i:X): ℝ:= ∑ j, ‖P i j‖
lemma cups_pos (P:Matrix X Y ℂ)(i:X): 0≤cusp P i:= sum_nonneg fun _ _=> norm_nonneg _
lemma cups_scale (P:Matrix X Y ℂ)(i:X)(r:ℂ): cusp (r • P) i=‖r‖ * cusp P i:=by unfold cusp; rw[mul_sum]; exact sum_congr rfl fun j _=>norm_mul ..
lemma cups_one (P:Matrix X Y ℂ)(i:X)(j:Y): ‖P i j‖≤ cusp P i:= single_le_sum (f:=fun j=> ‖P i j‖) (fun _ _=>norm_nonneg _) (mem_univ j)
lemma cups_add (P Q:Matrix X Y ℂ)(i:X) : cusp (P+Q) i ≤ cusp P i+cusp Q i:=by unfold cusp; rw [←sum_add_distrib]; exact sum_le_sum fun _ _=> norm_add_le ..
lemma cupful (P:Matrix X Y ℂ) (S : Finset Y)(i:X)(e:ℝ)(h:∀ j, ‖P i j‖≤ e)(ht:∀ j,P i j≠0 → j∈S): cusp P i ≤ S.card * e:=by unfold cusp; rw [← sum_subset (subset_univ S) (fun i h hm=>by rw [by_contra (fun hp=> hm (ht i hp)), norm_zero])]; exact (sum_le_sum (fun i _=> h i)).trans_eq (by simp)
lemma cups_tender(P:Matrix X Y ℂ)(R:Matrix Y Z ℂ)(s t:ℝ)(ht:0 ≤ t) (i:X)(hp:cusp P i≤ s)(h:∀ i,cusp R i ≤ t): cusp (P*R) i≤ s*t:=by
    unfold cusp at *; simp only [Matrix.mul_apply]; refine (sum_le_sum (fun j _=> norm_sum_le ..)).trans ?_; rw [sum_comm]; simp_rw [norm_mul,←mul_sum]; exact (sum_le_sum fun j _=> mul_le_mul_of_nonneg_left (h j) (norm_nonneg _)).trans (by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hp ht)
lemma cup_diff (P R:Matrix X Y ℂ)(s t C:ℝ)(S:Finset Y)(hs:0 ≤ s)(ht:0 ≤ t)(hc:(S.card:ℝ)≤ C)(x:X) (hr:∀ j,‖P x j‖ ≤ s)(he:cusp (P-R) x≤ t) (hq:∀ i,R x i≠0 → i∈S): cusp P x≤ t+C*(t+s):=by
    have hq:= cupful R S x (t+s) (fun j=> ?_) hq
    · refine Eq.trans_le (show cusp P x=cusp (P-R+R) x from by rw[sub_add_cancel]) ((cups_add (P-R) R x).trans ?_); exact add_le_add he (hq.trans (mul_le_mul_of_nonneg_right hc (add_nonneg ht hs)))
    refine le_trans (by apply norm_le_norm_sub_add _ (P x j)) (add_le_add ?_ (hr j)); rw [norm_sub_rev]; exact (cups_one (P-R) x j).trans he
end sum
-- cost budget of Dletter. stencil native. card erasures
noncomputable def clique (G:Gauge)(c:Side)(r:ℕ)(v:ℕ)(x:Site c) : Finset (FreeResolvent.Slot G c r):= (halo v {x}) ×ˢ univ
lemma clique_ion (x:Site c)(i:FreeResolvent.Slot G c r) : i∈clique G c r b x ↔ i.1∈ halo b {x}:=by simp [clique]
lemma clique_cost (x:Site c): (clique G c r b x).card ≤ (b+b+1)^4*Fintype.card (PAC G r):=by rw [clique,card_product,card_univ]; exact Nat.mul_le_mul_right _ (by simpa using Corona.halo_size ({x}:Support c) b)


end YM.Bloom.TreeP
#print axioms YM.Bloom.TreeP.churn
