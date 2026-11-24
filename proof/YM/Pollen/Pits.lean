import YM.Pollen.Rill
import YM.Massive.PCAC.Bare
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Lat Function Lattice Wilson Creek Grass Ledge Lat Finset NormedSpace RG Cove Cove.Send Filter Run
open MeasureTheory QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k N:ℕ}{t a b:ℝ}{o: Site c} {P:BudgetPoint}
open Further.DenseMixedKernels
local notation "M"=> Modes c N
local notation "Q"=>Sour M
set_option quotPrecheck false
local notation "ν" V:arg W:arg=> fun X:Grid c=>(applyMark false (V X) - applyMark true (W X)).toContinuousLinearMap
variable (x y:Grid c→ Sour (Modes c N))
local notation "Y"=> ν x y
variable {A D:Type*}[Fintype A][Fintype D]
lemma rotateV [DecidableEq D] (A:Sour D)(u:Sour D)(v:Sour D)(z:Dirac D)(h:A ∈ unitary _)(hv:v=A*u*star A)(b:Bool): applyMark b u (adapter A ((star A).transpose) z) = adapter A ((star A).transpose) (applyMark b v z):=by
    let f:=adapter A ((star A).transpose); have he(X Z:Sour D)(α:D→ Dirac D) (i:D) : ∑ j, X i j • ∑ k,Z j k • α k=∑ j,(X*Z) i j • α j:=by simp_rw [smul_sum,smul_smul,Matrix.mul_apply,sum_smul]; rw [sum_comm]
    refine through_mark f ?_ _; rintro (i|i) <;> cases b
    · change applyMark _ _ (f (psi i))= f (applyMark _ _ (psi i)); unfold f; rw [adapt_psi,leftP,map_sum,map_sum]; simp_rw [map_smul,leftP,adapt_psi,he]; rw[hv,mul_assoc (A*u),h.1,mul_one]
    · change applyMark _ _ (f (psi i))= f (applyMark _ _ (psi i)); unfold f; rw [adapt_psi,passP,map_zero,map_sum]; simp_rw [map_smul,passP,smul_zero,sum_const_zero]
    · change applyMark _ _ (f (bar i))= f (applyMark _ _ (bar i)); unfold f; rw [adapt_bar,passB,map_zero,map_sum]; simp_rw [map_smul,passB,smul_zero,sum_const_zero]
    change applyMark _ _ (f (bar i))= f (applyMark _ _ (bar i)); unfold f; rw [adapt_bar,leftB,map_sum,map_sum]; simp_rw [map_smul,leftB,adapt_bar]; change ∑ j,(star A).transpose i j • ∑ k,u.transpose j k • bar k=∑ j, v.transpose i j • ∑ k,(star A).transpose j k • bar k; rw [he,he,← Matrix.transpose_mul,← Matrix.transpose_mul, hv,←mul_assoc,←mul_assoc,h.1,one_mul]
private lemma wageE (i j:Keys c N) : Bean ((gen i j).toContinuousLinearMap)∧∀ (t:ℝ),0<t→∀ x:Fields c N, load (fun _=>t) (gen i j x)≤ load (fun _=>t) x:=by
    constructor
    · refine ⟨fun x=>?_, fun x y=> gen_mult i j x y⟩; change atom j*vary i _= Grass.grade (atom j*vary i x); rw[show vary i (Grass.grade x)= -Grass.grade (vary i x) from anti ..,map_mul,grade_atom,neg_mul,mul_neg]
    intro t ht x; let g:Keys c N→ℝ:=fun _=>t
    change load g (atom j*vary i x) ≤_; refine (load_mul g _ _).trans ?_; rw[load_atom g (fun _=> ht)]; change t*load g (vary i x)≤ _; exact (mul_le_mul_of_nonneg_left (fee g (fun _=>ht) i x) ht.le).trans_eq (mul_inv_cancel_left₀ ht.ne' _)
-- Spoke assumes nonzero only if hC.Fe etc. localOn.B weighed at origin then translate pitch.Se.E.
local notation "W" p:arg=> halo 1 {p}
def rangeH (p:Site c)(u: Finset (Site c))(v j:M):= v.1.1=p∧j.1.1∈u
structure Fetch (o:Site c)(b:Bool)(v: Grid c→ Sour (Modes c N))(P:BudgetPoint)(C:ℝ):Prop where
 reads : LocalOn (halo 1 {o}) v
 reach i j U:v U i j ≠ 0 → if b then rangeH o (halo 1 {o}) j i else rangeH o (halo 1 {o}) i j
 gauge x g : v (Lattice.gauge g x)= Lat.rotates N g*v x *star (Lat.rotates N g)
 nz:0 ≤ C
 sale : ∃ f:Modes c N→ Modes c N→ℝ,(∑ i,∑ j,f i j) ≤ C ∧ ∀ i j,0 ≤ f i j∧ Continuous (fun y:Grid c=>v y i j) ∧ ∀ z o', Pitch (fun y=>v y i j) z (P.dirBound o') P.order (f i j) ((1+(separation o o':ℝ))^P.power)
variable (h:Fetch o false x P a)(hp:Fetch o true y P b)
include h hp
set_option maxHeartbeats 780000 in
lemma populate (hv:∀ X:Grid c,(x X).trace=(y X).trace): Suit o P (a+b) (ν x y):=by
   let Wp:= Y; let D:= W o
   refine ⟨fun X=> ⟨fun i=>?_,fun i j=>?_⟩,fun X X' hv=>by rw[h.reads _ _ hv,hp.reads _ _ hv],fun i g u=>?_,fun i X u hu=>?_,fun i X hu v hX=>?_,fun X v=>?_,add_nonneg h.nz hp.nz,?_⟩
   ·
     change applyMark false (x X) (Grass.grade i)-applyMark true (y X) (Grass.grade i)=Grass.grade (_-_); rw [L_grade,L_grade,map_sub]
   · change applyMark false (x X) (i*j)-applyMark true (y X) (i*j)=(_-_)*_+_*(_-_); rw [LMark,LMark,sub_mul,mul_sub]; abel
   · change applyMark false (x i) _-applyMark true (y i) _=slots N g (_-_); rw [map_sub]; exact congr_arg₂ (·-·) (rotateV _ _ _ u (Lat.rotates_law N g) (h.gauge ..) _) (rotateV _ _ _ u (Lat.rotates_law N g) (hp.gauge ..) _)
   · let p:=region (limits (F:=N) (X∪ D)); change applyMark false (x i) u-applyMark true (y i) u∈p; apply Subalgebra.sub_mem _
     · rw [column]; apply Subalgebra.sum_mem _; intro j _; apply Subalgebra.sum_mem; intro v _; by_cases hz:x i j v=0; · rw[hz,zero_smul]; exact Subalgebra.zero_mem _
       have hh:rangeH o D j v:=h.reach _ _ i hz; apply p.smul_mem; change (atom (.inl v)* vary (.inl j) u)∈p; exact p.mul_mem (marked _ _ (mem_filter.mpr ⟨mem_univ _,mem_union_right X hh.2⟩)) (regionMon (limitsMon _ _ subset_union_left) (preserves _ hu))
     rw [row]; apply Subalgebra.sum_mem _; intro j _; apply Subalgebra.sum_mem; intro v _; by_cases hz:y i j v=0; · rw[hz,zero_smul]; exact Subalgebra.zero_mem _
     have hh:rangeH o D v j:=hp.reach _ _ i hz; apply p.smul_mem; change (atom (.inr j)*vary (.inr v) u)∈p; exact p.mul_mem (marked _ _ (mem_filter.mpr ⟨mem_univ _,mem_union_right X hh.2⟩)) (regionMon (limitsMon _ _ subset_union_left) (preserves _ hu)) -- hu hu
   · change applyMark false (x i) v-applyMark true (y i) v=0; rw [column,row,sum_eq_zero]; swap
     · intro j _; apply sum_eq_zero; intro k _; by_cases hx:x i j k=0; · rw [hx,zero_smul]
       have hh :rangeH o D j k:= h.reach _ _ _ hx; have hf:vary (Sum.inl j) v=0:= lock _ hX (fun h=>hu (hh.1 ▸ (show j.1.1∈ X from (mem_filter.mp h).2))); change _ • (atom _*vary (Sum.inl j) v) = _; rw [hf,mul_zero,smul_zero]
     rw [sum_eq_zero,sub_self]; intro j _; apply sum_eq_zero; intro k _; by_cases hx:y i j k=0; · rw [hx,zero_smul]
     have hh:rangeH o D k j:=hp.reach _ _ _ hx; have hf:vary (.inr k) v=0:=lock _ hX fun h=>hu (hh.1 ▸ (show k.1.1∈ X from (mem_filter.mp h).2)); change _ • (atom _*vary (.inr k) v)=_; rw [hf,mul_zero,smul_zero]
   · change ber _ (applyMark false _ v-applyMark true _ v)=_; rw[map_sub,integrated,integrated,hv,sub_self]
   obtain ⟨f,hf,hF⟩:=h.sale; obtain ⟨g,hg,hG⟩:=hp.sale; let α:=M × M
   let V(i:M × M):=(gen (.inl i.1) (.inl i.2) (A:=Pairs M)).toContinuousLinearMap; let Zt(i:M × M):=(gen (.inr i.2) (.inr i.1) (A:=Pairs M)).toContinuousLinearMap
   let A(i:α)(X:Grid c):= x X i.1 i.2; let B(i:α)(X:Grid c):= -y X i.1 i.2
   refine ⟨α⊕α,inferInstance,Sum.elim V Zt, Sum.elim A B, Sum.elim (fun i=>f i.1 i.2) (fun i=>g i.1 i.2),fun _=>1,?_, ?_,fun X=> ?_⟩
   · rw [Fintype.sum_sum_type]; unfold α; simp only [Fintype.sum_prod_type,mul_one,Sum.elim_inl,Sum.elim_inr] at hf hg ⊢; exact add_le_add hf hg
   · rintro (i|i)
     · obtain ⟨hf,hg,hh⟩:= hF i.1 i.2; exact ⟨(wageE ..).1,zero_le_one,hf,hg,hh,fun t ht x'=> (wageE (Sum.inl i.1) (Sum.inl i.2)).2 t ht x'|>.trans_eq (Eq.symm (one_mul _))⟩
     obtain ⟨hf,hg,hh⟩:= hG i.1 i.2; exact ⟨(wageE ..).1,zero_le_one,hf,hg.neg,fun z p=> (hh z p).negate,fun t ht x'=> ((wageE (Sum.inr i.2) (Sum.inr i.1)).2 t ht x').trans_eq (Eq.symm (one_mul _))⟩
   ext1 u; simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,LinearMap.coe_toContinuousLinearMap',LinearMap.sub_apply]; unfold α V Zt A B; simp only [column,row,ContinuousLinearMap.smul_apply,Fintype.sum_prod_type, neg_smul,sum_neg_distrib, LinearMap.coe_toContinuousLinearMap']; rw [sub_eq_add_neg] -- adjust
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.populate
