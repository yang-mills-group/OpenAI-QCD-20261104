import YM.QCD.Nola.Cells
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι κ A:Type*} {n : Side} {k:ℕ} [Fintype A]{p:A→Site n} {s t a χ δ b:ℝ}
open Kites Pads
namespace Pads
lemma stars (S:Pads p ι κ)(hs:∀ i,(S.leaves (.inl i)).Nonempty) (s:S.Join): (unionK S s).Nonempty:=by
   obtain ⟨i,hi⟩:=s.property.2; obtain ⟨x,hx⟩:= hs i; exact ⟨x,mem_biUnion.mpr ⟨Sum.inl i,Finset.mem_toLeft.mp hi,hx⟩⟩
lemma starP (S:Pads p ι κ)(i: S.Join): light A (S.unite i)∈ region (alphabet (p:=p) (S.unionK i)):= (S.shire i.1).2
def scroll (S:Pads p ι κ)(i:Clusters S.Join) :=termP (blocked S.unionK) S.unite i
def walkH (S:Pads p ι κ)(i:Clusters S.Join) := unionOf S.unionK i.2
lemma platelet (V X:Support n)(h:V⊆X): alphabet (p:=p) V⊆ alphabet (p:=p) X:= fun i hi=> mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp hi).2⟩
lemma regionP (S:Pads p ι κ)(i:Clusters S.Join): light _ (S.scroll i)∈region (alphabet (p:=p) (S.walkH i)):=by
    let Q:=region (alphabet (p:=p) (S.walkH i)); let d := fun j=> S.unite (i.2 j); have ht (u:Finset (Option (Fin i.1))): light _ (∏ j∈u,d j)∈ Q:=by
           induction u using Finset.induction_on with
           | empty=> rw [prod_empty,map_one]; exact Q.one_mem
           | insert a t ha ih=> rw [prod_insert ha,map_mul]; exact Q.mul_mem (regionMon (platelet _ _ (subset_biUnion_of_mem (S.unionK∘i.2) (mem_univ a))) (starP ..)) ih
    unfold scroll termP; let z:ℝ:= ((i.1+1).factorial:ℝ)⁻¹; let a:= coefficient (blocked S.unionK) i.2 -- int? coefficient ℝ
    have hv(b:ℝ)(X:Patio A): light A (b • X)=(b:ℂ) • light A X:= (map_smul (Cove.light A) (b:ℂ) X)
    rw [hv,hv]; exact Q.smul_mem (Q.smul_mem (ht _) _) _
lemma scaled (S:Pads p ι κ)(i:Clusters S.Join): tyre t (S.scroll i)= termP (blocked S.unionK) (tyre t ∘ S.unite) i:=by
    unfold scroll termP; have hp (z:ℝ)(y:Patio A): tyre t (z • y)= z • tyre t y:=map_smul _ (z:ℂ) _
    rw [hp,hp,map_prod]; rfl
variable (S:Pads p ι κ) (b: ι ⊕ κ→ℝ)(hp:∀ i,0 ≤ b i)
variable {m:ℕ}(g:ι⊕κ→ℝ)(hg:∀ i,0 ≤ g i)(he:∀ i, b i*tell (S.leaves i) m ≤ (if i.isLeft then χ else 1)*g i)
include hp hg
lemma lowering (u:S.Join) (h:χ≤1)(hx:0 ≤ χ) (hi:∀ i, b i*tell (S.leaves i) m ≤ (if i.isLeft then χ else 1)*g i):(taxon S b u)*tell (unionK S u) m ≤χ* taxon S g u :=by
    obtain ⟨i,ht⟩:= u.property.2; let f(i:ι⊕κ):ℝ:= if i.isLeft then χ else 1; have hr(i):0≤f i:=by unfold f; split <;> positivity
    refine le_trans (S.tents b hp (fun i=> f i*g i) (fun i=> mul_nonneg (hr i) (hg i)) hi u) ?_; unfold taxon; rw [prod_mul_distrib]; apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _=>hg i); rw [← Finset.mul_prod_erase _ _ (Finset.mem_toLeft.mp ht),show f (.inl i)=χ from rfl]; apply mul_le_of_le_one_right hx; exact prod_le_one (fun i _=> hr i) (fun i _=>by unfold f; split <;> first| exact h|exact le_rfl)
variable [Fintype ι][Fintype κ]
include he
lemma thrills (hχ:χ>0)(hl:χ≤1)(hz:0<t)(hx:∀ i, ‖tyre t (S.source i)‖ ≤ b (.inl i))(ht:∀ i x, load (fun _=> t) (S.buys i x) ≤ b (.inr i)* load (fun _=> t) x) (hG:Ac.HitCard S.leaves g 2 a)(ha:a>0)(hk:a ≤ 1)(hr:degreePriceCard (Real.exp a-1) 1 ≤1/2) (hs:∀ i,(S.leaves (.inl i)).Nonempty)(hb:∀ i,S.buys i (1:Alg A)=0) :
      let W:= fun i=> termP (blocked S.unionK) (tyre t∘ S.unite) i; let H:= logS (blocked S.unionK) S.unite
      HasSum S.scroll H ∧ (HasSum W (tyre t H)) ∧ NormedSpace.exp H = ∑ i,S.ham i ∧ SumBudget (fun i=>‖W i‖ * tell (S.walkH i) m) ((Fintype.card (Site n):ℝ)*(χ*(Real.exp a-1))*2) ∧∀ x, SumBudget (fun i => if x∈ S.walkH i then ‖W i‖*tell (S.walkH i) m else 0) (χ*(Real.exp a-1)*2):=by
     intro W H; let g' i:= χ*S.taxon g i; let Y:=tyre t∘ S.unite; let p':=S.unionK; let r:=χ*(Real.exp a-1); have hw i: ‖Y i‖*tell (p' i) m ≤g' i := le_trans (mul_le_mul_of_nonneg_right (better S b hp hx ht i.1) (zero_le_one.trans (tell_one ..))) (S.lowering b hp g hg i hl hχ.le he) -- potential hp/hg ignored not included
     have hy : 0<Real.exp a-1:= sub_pos.mpr (Real.one_lt_exp_iff.mpr ha); have hu :0< r:=mul_pos hχ hy; have hm :r ≤ Real.exp a-1:=mul_le_of_le_one_left hy.le hl
     have hv : Trees.ReadyCard p' g' 0 r 1 (1/2):=by
           refine ⟨hu,zero_lt_one,(?_ : degreePriceCard r 1 ≤ degreePriceCard (Real.exp a-1) 1).trans hr,(by norm_num),fun i=>mul_nonneg hχ.le (prod_nonneg (s:=i.1) fun j _=>hg j),?_⟩ -- order? degreePriceCard retains B?
           · unfold degreePriceCard stretchCard; gcongr
           intro x; refine budget_mono (budget_scale hχ.le (S.thirst g hg 1 zero_le_one (by norm_num; exact hG) hk ha.le x)) (fun i=>by split; exact mul_nonneg (hw i|>fun h=>le_trans (mul_nonneg (norm_nonneg _) (zero_le_one.trans (tell_one ..))) h) (Real.exp_pos _).le; exact le_rfl) fun i=>?_ ; -- rewrite cases
           split
           next h' => unfold g'; norm_num [mul_assoc,p']
           next h'=> simp
     obtain ⟨hv',hx'⟩:= novels p' Y g' m (stars S hs) hw hv; let F:= (tyre t⁻¹:Patio A→ₐ[ℂ] _); let G:= (tyre t: Patio A→ₐ[ℂ] _)
     have hh(i):F (W i) = S.scroll i:= (congrArg F (scaled S i|>.symm)).trans (outP _ hz); have hW : HasSum S.scroll (F (logS (blocked p') Y)):=by
            exact (hv'.mapL F.toLinearMap.toContinuousLinearMap).congr_fun (fun i=> (hh i).symm) -- edit
     have h: H= F (logS (blocked p') Y):= hW.tsum_eq
     have hK : tyre t (F (logS (blocked p') Y))= logS (blocked p') Y:=by
            have he:= outP (logS (blocked p') Y) (inv_pos.mpr hz); rw [inv_inv] at he; exact he
     rw [h]; refine ⟨hW,?hsPre,?_ ,budget_loosen (risesP p' Y g' m (stars S hs) hw hv) ?_, fun x=>budget_loosen (movie p' Y g' m (stars S hs) hw hv x) ?_⟩
     case hsPre=> rw [hK]; exact hv'
     · rw [← NormedSpace.map_exp F F.toLinearMap.continuous_of_finiteDimensional,hx']; unfold totalP; rw [tsum_fintype, S.canvas hb,GasP.totalP,tsum_fintype,map_sum]; refine sum_congr rfl fun i _=> ?_; unfold valueP; by_cases he: Gas.separated (blocked S.unionK) i; swap; · exact (by rw [if_neg he,if_neg he]; exact map_zero F)
       rw [if_pos he,if_pos he,map_prod]; apply prod_congr rfl; intro j _; exact outP (S.unite j) hz
     · apply le_of_eq; norm_num; unfold r; ring
     apply le_of_eq; norm_num; rfl
end Pads
end YM.QCD.Nola
