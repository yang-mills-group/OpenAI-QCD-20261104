import YM.QCD.Ruby.Cars
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
/-! # single rooted large passenger sets. keep count soft by logs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}{a u v w A:ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {p :ι→ℝ} {q:β→ℝ}
lemma expanded (x y :ℝ) (h:1≤y) : 1+(Real.exp x-1)*y ≤ Real.exp (x*y):=by
   have hy:= zero_lt_one.trans_le h
   let a:=1/y; have ha:0≤a:=by unfold a; positivity
   have hb:a≤1 := (div_le_self (by norm_num) h); have hc:= convexOn_exp.2 (Set.mem_univ (x*y)) (Set.mem_univ (0:ℝ)) ha (sub_nonneg.mpr hb) (by ring)
   simp only [smul_eq_mul,mul_zero,add_zero,Real.exp_zero,mul_one] at hc; unfold a at hc; field_simp at hc; rw [mul_comm x y]; nlinarith
lemma exploded (x y : ℝ)(hx:0≤x)(h:1 ≤ y): (Real.exp x-1)*y ≤ (x*y)*Real.exp (x*y):=by
   have he:=expanded x y h; have h' := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (- (x*y))) (Real.exp_pos (x*y)).le; rw [Real.exp_neg,add_mul,inv_mul_cancel₀ (Real.exp_ne_zero _)] at h' -- need add_mul
   linarith
lemma totals_r (z: Finset ι)(h: 0 ≤ p): ∀ (r:ι→ℝ), (∀ i,1≤ r i)→ ∑ s ∈z.powerset, (∏ i∈s,(Real.exp (p i)-1)* r i) ≤ Real.exp (∑ i∈z,p i*r i):=by
   intro r hr; rw [← prod_add_one,Real.exp_sum]; apply Finset.prod_le_prod
   · intro i _; have hh:=Real.one_le_exp (h i); have hf : 0<r i:= zero_lt_one.trans_le (hr i); bound
   intro i _; rw [add_comm]; exact expanded _ _ (hr i) -- syntax
lemma marked_r (z:Finset ι) (i:ι)(hz:i∈z)(h:0≤p): ∀ (r:ι→ℝ),(∀ i,1≤r i) → ∑ s∈ z.powerset with i∈s,(∏ j∈s,(Real.exp (p j)-1)*r j) ≤ p i*r i*Real.exp (∑ i∈z,p i*r i):=by
   intro r hr; let f j:=(Real.exp (p j)-1)* r j; have hf i:0≤ f i:=mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (h i))) (zero_le_one.trans (hr i)); let u:= z.erase i
   have hp : z.powerset.filter (fun s=> i∈s)= u.powerset.image (fun s=> insert i s):=by
      ext s; constructor
      · intro hs; obtain ⟨he,ht⟩:=mem_filter.mp hs; exact mem_image.mpr ⟨_,mem_powerset.mpr (erase_subset_erase _ (mem_powerset.mp he)),insert_erase ht⟩
      intro hs; obtain ⟨w,hw,rfl⟩:=mem_image.mp hs; exact mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hz ((mem_powerset.mp hw).trans (erase_subset ..))),mem_insert_self ..⟩
   have he s (hs:s∈u.powerset):i∉s:=fun h=> notMem_erase _ _ ((mem_powerset.mp hs) h)
   rw [hp,sum_image]; swap; · rintro a ha b hb he'; change insert i a=insert i b at he'; exact (erase_insert (he a ha)).symm.trans ((congr_arg (fun s:Finset ι=>s.erase i) he').trans (erase_insert (he b hb)))
   let R j:=p j*r j; have hh : ∑ j∈z,R j=R i +∑ j∈u,R j:=(add_sum_erase _ _ hz).symm
   change ∑ s∈u.powerset, (∏ j∈insert i s, f j) ≤ R i*Real.exp _
   rw [show (∑ s∈u.powerset, (∏ j∈insert i s, f j))=f i*∑ s∈u.powerset, (∏ j∈s,f j) from ?_, show (∑ j∈z,p j * r j)=_ from hh, Real.exp_add, ← mul_assoc]
   rotate_left; · rw [mul_sum]; exact sum_congr rfl fun j hj=> prod_insert (he j hj)
   apply (mul_le_mul_of_nonneg_left (totals_r u h r hr) (hf i)).trans; exact mul_le_mul_of_nonneg_right (exploded _ _ (h i) (hr i)) (Real.exp_pos _).le
variable {D : Support c}
lemma cast (h:Ac.Hit Y.bud B p a A) (hu:0≤p) (s:Finset ι) (hs:∀ i∈s,¬Disjoint (Y.bud i) D): ∑ j∈s,p j*currency B a (Y.bud j) ≤ D.card*A :=by
    let f y j:= if y∈Y.bud j then p j*currency B a (Y.bud j) else 0
    have hh i (hi:i∈s): p i*currency B a (Y.bud i)≤ ∑ j∈D,f j i :=by
       obtain ⟨z,hz,hp⟩:=not_disjoint_iff.mp (hs i hi); apply le_trans (b:=f z i) _ (single_le_sum (fun j _=>(h j).1 i) hp); exact (if_pos hz).symm.le
    apply (sum_le_sum hh).trans; rw [sum_comm]; exact (sum_le_sum fun i _=> budget_sum (h i) s).trans_eq (by rw [sum_const,nsmul_eq_mul])
lemma sale (a b:Car Y X)(h:a.site=b.site)(he:a.bag=b.bag):a=b:=by cases a; cases b; congr
abbrev pick (p:ι→ℝ) (B:ℕ)(a:ℝ)(z: Car Y X):= ∏ i∈z.bag, (Real.exp (p i)-1)*currency B a (Y.bud i) -- parenthesization Lean caution ∏ extends
lemma lead (u:Finset (Car Y X)){i:β} (w:Support c) (hg:Ac.Hit Y.bud B p a A) (h:0≤p) (hh:∀ j∈u,j.site=i)(hv:0≤a):
   let d:=(oriD X i).card
   (∑ j∈u,pick Y X p B a j) ≤ Real.exp (d*A) ∧(∀ x:ι,(∀ j∈u,x∈j.bag) → ∑ j∈u,pick Y X p B a j ≤ p x*currency B a (Y.bud x)*Real.exp (d*A)):=by
   let z:= u.biUnion Car.bag; let f(j:Finset ι):ℝ:= ∏ i∈j,(Real.exp (p i)-1)*currency B a (Y.bud i)
   let V i:= currency B a (Y.bud i); have ht i:1≤ V i:= Real.one_le_exp (mul_nonneg hv (by positivity))
   have he j :0≤ f j:= prod_nonneg fun i _=> mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (h i))) (zero_le_one.trans (ht i))
   let s:=u.image Car.bag; have hs : ∑ j∈u,pick Y X p B a j=∑ j∈s,f j:= Eq.symm (sum_image (fun v hv w hw h=> sale Y X v w ((hh v hv).trans (hh w hw).symm) h))
   have hx : s⊆ z.powerset:=by intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact mem_powerset.mpr (subset_biUnion_of_mem _ hj)
   intro d; have hy : Real.exp (∑ i∈z,p i*V i) ≤ Real.exp (d*A):=by
      apply Real.exp_monotone; apply cast Y hg h; intro j hj; obtain ⟨k,hk,hj⟩:=mem_biUnion.mp hj; exact hh k hk ▸ k.closeD j hj
   rw [hs]; constructor
   · exact (sum_le_sum_of_subset_of_nonneg hx (fun i _ _=> he i)).trans ((totals_r z h _ ht).trans hy)
   intro x hV; by_cases hz: x ∈ z
   · apply le_trans _ ((marked_r z x hz h _ ht).trans (mul_le_mul_of_nonneg_left hy (mul_nonneg (h _) (zero_le_one.trans (ht _)))))
     apply sum_le_sum_of_subset_of_nonneg _ (fun i _ _=> he i); intro i hi; refine mem_filter.mpr ⟨hx hi,?_⟩; obtain ⟨p,hp,rfl⟩:=mem_image.mp hi; exact hV p hp
   rw [show s=∅ from Finset.eq_empty_iff_forall_notMem.mpr ?_,sum_empty]; rotate_left; · intro i hi; obtain ⟨j,hj,hx⟩:=mem_image.mp hi; exact hz (mem_biUnion.mpr ⟨j,hj,hV j hj⟩)
   exact mul_nonneg (mul_nonneg (h _) (zero_le_one.trans (ht _))) (Real.exp_pos _).le
end YM.QCD.Ruby
