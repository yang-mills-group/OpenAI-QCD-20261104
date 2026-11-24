import YM.QCD.Nola.Front
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef
open scoped BigOperators Classical Topology ContDiff
variable {ι K : Type*}[NormedCommRing K][NormOneClass K][NormedAlgebra ℝ K][NormedAlgebra ℚ K][CompleteSpace K]
variable {n : Side} {l k : ℕ}{X Y : Support n}
variable (p : ι→Support n)(W : ι→K)(w:ι→ℝ)(m:ℕ)(hp:∀ i,(p i).Nonempty) (hw:∀ i, ‖W i‖*tell (p i) m ≤ w i) {a δ d v:ℝ}(h:Trees.ReadyCard p w 0 a δ d)
noncomputable def cost (i:Ursell.Clusters ι):ℝ:= ‖termP (blocked p) W i‖*tell (unionOf p i.2) m
lemma test (i:Ursell.Clusters ι): 0 ≤ cost p W m i:=mul_nonneg (norm_nonneg _) (zero_le_one.trans (tell_one ..))
include h hp hw
lemma curtain (i:Ursell.Clusters ι): cost p W m i ≤ clusters (blocked p) (chargeCard p w 0) i.2:=by
    let U j:= tell (p j) m; let R:= blocked p; have hs(i):0 ≤ U i:=zero_le_one.trans (tell_one _ _); have hy:∀ i,chargeCard p w 0 i=w i:= fun i=>by simp [chargeCard,currencyCard]
    let V(i:ι):=‖W i‖
    by_cases hh: coefficient R i.2=0; swap
    · have hk : ‖termP R W i‖≤ clusters R V i.2:= GasP.term_bill (fun _=> le_rfl) _ -- check
      have H : tell (unionOf p i.2) m≤ ∏ j,U (i.2 j):= tarot (p ∘ i.2) univ (ash p i.2 (literal_test p hp) hh) m
      refine (mul_le_mul hk H (zero_le_one.trans (tell_one ..)) (clusters_nonneg R (fun _=>norm_nonneg _) _)).trans ?_
      unfold clusters; simp only [hy,div_mul_eq_mul_div,mul_assoc,← prod_mul_distrib]; gcongr; exacts [fun i _=> mul_nonneg (norm_nonneg _) (hs _),hw _] -- deps
    change ‖termP R W i‖*_ ≤ clusters R _ _; unfold termP clusters; simp [hh]
-- per length hit & sum
lemma stellar (x:Site n)(j:ℕ): SumBudget (fun i: Ursell.Tuple ι j=> if x∈ unionOf p i then cost p W m ⟨j,i⟩ else 0) (a*d^j):=by
    let s (i:ι): Prop:= x∈p i; have ht : SumBudget (Ursell.chargeCard p (marked s w) (0+δ)) a:=by convert test_hitCard p h x using 1; ext i; simp [chargeCard,s,Trees.hit,marked]
    have hc:= cluster_atCard (blocked p) p (literal_test p hp) s h ht j
    refine budget_mono hc (fun i=>by split <;> first| exact test p W m _| exact le_rfl) fun i=>?_; split
    next hx=> obtain ⟨w₀,ha,hv⟩:=mem_biUnion.mp hx; rw [if_pos (show ∃ i',s (i i') from ⟨w₀,hv⟩)]; exact curtain p W w m hp hw h _
    next ha=> exact hc.1 i
lemma movie (x:Site n):SumBudget (fun i: Ursell.Clusters ι=> if x∈ unionOf p i.2 then cost p W m i else 0) (a*(1-d)⁻¹):=by
    have hh:= h.2.2.2.1
    simpa only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] using sigma_tail (fun i: Ursell.Clusters ι=> if x∈unionOf p i.2 then cost p W m i else 0) (stellar p W w m hp hw h x) h.1.le (ready_posCard p h).le hh 0
lemma salaried {I: Type*} {X:I → Support n} {g:I→ℝ}(hs:∀ i,(X i).Nonempty)(hg:∀ i,0≤g i)(hv:∀ x,SumBudget (fun i=> if x∈X i then g i else 0) v): SumBudget g ((Fintype.card (Site n):ℝ)*v):=by
    have hh:= budget_over univ (fun x i=> if x∈ X i then g i else 0) (fun _=> v) (fun i _=> hv i)
    rw [sum_const,card_univ,nsmul_eq_mul] at hh; apply budget_mono hh hg; intro i; obtain ⟨u,hu⟩:= hs i; refine Eq.trans_le (if_pos (t:=g i) (e:=(0:ℝ)) hu).symm (single_le_sum (fun a _=> (hv a).1 i) (mem_univ u))
include h
lemma risesP : SumBudget (cost p W m) ((Fintype.card (Site n):ℝ)*(a*(1-d)⁻¹)):=by
     refine salaried p W w m hp hw h (X:=fun i=>_) ?_ (test p W m) (movie p W w m hp hw h); rintro ⟨i,u⟩; obtain ⟨x,hx⟩:= hp (u none); exact ⟨x,mem_biUnion.mpr ⟨none,mem_univ _,hx⟩⟩
lemma teaches (i):‖termP (blocked p) W i‖ ≤ cost p W m i:=le_mul_of_one_le_right (norm_nonneg _) (tell_one ..)
lemma novels [Fintype ι]: let S:= logS (blocked p) W; HasSum (termP (blocked p) W) S ∧ NormedSpace.exp S=totalP (blocked p) W:=by
    intro S; let f:=termP (blocked p) W; have hb:= budget_mono (risesP p W w m hp hw h) (fun i=>norm_nonneg (f i)) (teaches p W w m hp hw h)
    have ht:Summable f:=hb.2.1.of_norm; refine ⟨ht.hasSum,?_⟩
    let V:= (Fintype.card (Site n):ℝ)
    let q:= (∑' i, GasP.logRow (blocked p) W i)
    have he:S=q:=by unfold S logS; rw [ht.tsum_sigma]; unfold q; exact tsum_congr fun i=>by simp only [GasP.logRow_open,tsum_fintype,f]
    rw [he,totalP,tsum_fintype]; refine GasP.exact_polynomial (blocked p) W ⟨fun i=>Or.inl rfl, fun _ _=>blocked_back p⟩ (show 0≤ V*a from mul_nonneg (Nat.cast_nonneg _) h.1.le) (ready_posCard p h) h.2.2.2.1 ?_ -- hr
    intro i; rw [GasP.logRow_open]; apply (norm_sum_le ..).trans
    have hu :SumBudget (fun j:Ursell.Tuple ι i=>cost p W m ⟨i,j⟩) (V*(a*d^i)):= by
          refine salaried p W w m hp hw h (X:=unionOf p) (fun j=>?_) (fun j=>test ..) (fun x=>stellar p W w m hp hw h x i); obtain ⟨x,hx⟩:=hp (j none); exact ⟨x,mem_biUnion.mpr ⟨none,mem_univ _,hx⟩⟩
    rw [mul_assoc]; exact budget_sum (budget_mono hu (fun i=> norm_nonneg _) (fun i=> teaches p W w m hp hw h _)) _ -- edit
end YM.QCD.Nola
