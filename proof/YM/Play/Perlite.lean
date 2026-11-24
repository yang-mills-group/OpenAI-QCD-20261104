import YM.Play.Cave
import YM.Play.Cot
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace Cupola Ribbon QCD.Bera QCD.Anomaly
open MeasureTheory BigOperators Matrix
open scoped Topology BigOperators ContDiff Classical
variable {I A B G E: Type}[Fintype I][Fintype A]{X Y M: Finset I}
namespace Chamber
local notation "Z"=> A⊕Spine I
local notation "Zb"=> B⊕Spine I
local notation "Δ"=> Patio Z
variable {q:I→Bool}
local notation "mk"=> VaultP A q
lemma vp {T:Type}{f:T→Δ}{v:T→Finset I}(u:Finset T)(h:∀ i∈u,f i∈ mk (v i)): (∏ i∈u,f i)∈ mk (u.biUnion v):=by
     induction u using Finset.induction_on with
     | empty=>rw [Finset.prod_empty,biUnion_empty]; exact polite_empty_one q
     | insert i u hi ih=> rw [prod_insert hi,biUnion_insert]; exact Polite.attached (h i (mem_insert_self ..)) (ih (fun _ h'=>h _ (mem_insert_of_mem h')))
lemma parcel (f: Finset I→Δ) (h:∀ i∈X.powerset,(f i)∈mk i): parties f X∈mk X:= by
    apply Submodule.sum_mem; intro i hi; have hz: i.biUnion id=X:=(mem_filter.mp hi).2.2.1; rw [← hz]; exact vp (v:=id) i (fun j hj=> h j (mem_powerset.mpr (member hi hj).2))
lemma smash {f g:Δ}{s t:Finset I}(h:f∈mk s)(he:g∈mk t)(hv:¬ Disjoint s t): f*g=0:=Polite.nilpotent h he hv
lemma launch {f:Δ} (h:f∈mk X)(hp:X.Nonempty): exp f=1+f:=by
   have hh:f^2=0:=by rw [pow_two]; exact smash h h (fun he=>by obtain ⟨x,hx⟩:=hp; exact Finset.disjoint_left.mp he hx hx)
   have he:= exp_series_hasSum_exp' (𝕂:=ℂ) f; refine he.tsum_eq.symm.trans (Eq.trans (tsum_eq_sum (s:=range 2) (?_)) (?_)); · intro i hi; rw [mem_range] at hi; rw [show f^i=0 from pow_eq_zero_of_le (le_of_not_gt hi) hh]; exact smul_zero _
   simp [Finset.sum_range_succ]
lemma source (f:Finset I →Δ) (X:Finset I)(h:∀ v∈ X.powerset,f v∈mk v):
   NormedSpace.exp (∑ v∈X.powerset.erase ∅, f v) = ∑ i∈X.powerset,parties f i:=by
     let i := X.powerset.erase ∅
     have ht (p:Finset (Finset I)): exp (∑ i∈p,f i)= ∏ i ∈p,exp (f i):=by
         induction p using Finset.induction_on with
         | empty=> simp
         | insert a s ha ih=> rw [sum_insert ha,prod_insert ha,exp_add,ih]
     rw [ht, prod_congr rfl (g:=fun v=>1+f v) (fun v hv=> launch (h v (mem_of_mem_erase hv)) (Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_erase hv))), signal f X (fun i hi j hj=> smash (h i hi) (h j hj))]
lemma issue (f:Finset I→Δ)(X:Finset I) (h:∀ i∈X.powerset,f i∈mk i)(j:Finset I)(hh:j⊆ X): (Cupola.pick A q j) (exp (∑ v∈ X.powerset.erase ∅, f v))= parties f j:=by
     have hf i(hi:i⊆ X): parties f i∈ mk i:= parcel f fun v hv=> h v (mem_powerset.mpr ((mem_powerset.mp hv).trans hi))
     rw [source f X h,map_sum,sum_eq_single j, eq_pick _ _ _ _ (hf _ hh)]
     intro i hi he; let f' :=parties f i; apply Subtype.ext; change stake A (burst q j) (scrape A _ f'.val)=0; rw [Polite.spectral (hf _ (mem_powerset.mp hi)) _ (fun hg=> he (burstUnique q hg.symm)),map_zero]; simp [hh]
lemma costProj (q:I→Bool)(i: Finset I)(x:Δ): ‖Cupola.pick A q i x‖≤‖x‖:=by
   let s:=burst q i; let Z':= x.val; change ‖stake A s (scrape A s Z')‖ ≤ ‖Z'‖; -- Via l1 projection.W
   conv => lhs; rw [← Ribbon.rewriteR A Z',map_sum,map_sum]
   rw [sum_eq_single s]
   · rw [quid]; -- use fiscal or sign.Composition. norm stake equals. 
     let f(i:A):= (1:ℝ); let g(i:Spine I):= (1:ℝ)
     have he (x:Alg (A⊕Spine I)): ‖x‖= Creek.load (expRate (p:=f) (q:=g)) x:=by
        rw [Grass.norm_def, Creek.dry (expRate (p:=f) (q:=g)) (fun a=>by cases a <;> exact zero_lt_one)]; apply Finset.sum_congr rfl; intro y _; rw [Finset.prod_eq_one (fun i _=>by rcases i with i|i <;> rfl), one_mul]
     rw [he,he Z', stakesBill (p:=f) (q:=g) (fun _=>zero_lt_one) (fun _=>zero_lt_one), fiscal (p:=f) (q:=g) (fun _=>zero_lt_one) (fun _=>zero_lt_one)]; unfold g; simp only [prod_const_one,one_mul]; exact single_le_sum (f:=fun i'=>load f (scrape A i' Z')) (fun i' _=> load_nn ..) (mem_univ s)
   · intro j _ hi; rw [stakesX,if_neg hi.symm,map_zero]
   · simp

-- polynomial layers
open MvPolynomial
local notation "F"=> Papers G Δ
abbrev coined (G A I:Type)[Fintype A][Fintype I](q:I→Bool) (s: Finset I): Submodule ℂ (Papers G (Patio (A⊕Spine I))) := vault (VaultP A q s)
local notation "wk"=> coined G A I q
lemma sealed {f g:F} (h:f∈wk X)(he:g∈wk Y): f*g∈wk (X∪Y):=by
    rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]; apply Submodule.sum_mem; intro i hi; apply Submodule.sum_mem; intro j hj; rw [show monomial _ (coeff _ f*coeff _ g)=outer (monomial (i+j) 1) _ from (by rw [outmono,one_smul])]; exact outVault _ (Polite.attached (h i) (he j))
lemma oncQ : (1:F)∈ wk ∅:=by rw [show (1:F)=outer 1 1 from (by simp [outP])]; exact outVault _ (polite_empty_one q)
lemma melt {f g:F} (h:f∈wk X)(he:g∈wk Y)(hk:¬ Disjoint X Y): f*g=0:=by
    rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]; apply sum_eq_zero; intro i _; refine sum_eq_zero fun j _=> ?_; rw [smash (h i) (he j) hk,map_zero]
lemma brush {T:Type}{f:T→F}{v:T→Finset I}(u:Finset T)(h:∀ i∈u,f i∈wk (v i)): (∏ i∈u,f i)∈wk (u.biUnion v):=by
    induction u using Finset.induction_on with
    | empty=>rw [Finset.prod_empty,biUnion_empty]; exact oncQ
    | insert i u hi ih=> rw [prod_insert hi,biUnion_insert]; exact sealed (h i (mem_insert_self ..)) (ih (fun _ h'=>h _ (mem_insert_of_mem h')))
lemma planks {f:Finset I→F}(h:∀ i⊆X, i.Nonempty→f i∈ wk i): parties f X∈wk X:=by
    refine Submodule.sum_mem _ fun i hi=>?_ ; rw [show X=i.biUnion id from (mem_filter.mp hi).2.2.1.symm]; exact brush (v:=id) i (fun j hj=> h _ (member hi hj).2 (member hi hj).1)
lemma caveat {f:Finset I→F}(h:∀ i⊆X, i.Nonempty→ f i∈wk i): cetacea f X∈wk X:=by
    suffices hv:∀ n:ℕ,∀ v ⊆ X,v.card=n → cetacea f v∈wk v from hv _ X (Subset.refl _) rfl
    intro n; induction n using Nat.strong_induction_on with
    | h n ih=>
      intro i hi hp; rw [cet]; split; swap; · apply Submodule.zero_mem _
      next he=> refine Submodule.sub_mem _ (h i hi he) (Submodule.sum_mem _ fun j hj=>?_); have hv:=(mem_of_mem_erase hj); rw [show i=j.biUnion id from (mem_filter.mp hv).2.2.1.symm]; exact brush (v:=id) j (fun k hk=> ih _ ((card_lt_card (limit hj hk)).trans_le hp.le) k ((member hv hk).2.trans hi) rfl)
variable [Fintype B] [Fintype G] [Fintype E]
def foamW (M:Matrix A B ℂ)(U:Matrix A A ℂ)(Gv:Matrix G E ℂ)(C:YM.Next.Rank.Normal.Symmetric G) :=
    shootsW Gv C (breezeP (Spine I) M) (breezeX (Spine I) U)
lemma clouds (M:Matrix A B ℂ)(U:Matrix A A ℂ)(Gv:Matrix G E ℂ)(C:YM.Next.Rank.Normal.Symmetric G){p:F}(h:p∈wk X): foamW (I:=I) M U Gv C p∈coined E B I q X:=by
    refine intoVault h _ _ (fun i hi=> politeStep ((changeVars M).toLinearMap.toContinuousLinearMap.comp (birth (Wand U))) (h i) (?_)); exact rimy (Spine I) U M (coeff i p)
end Chamber
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Chamber.clouds
#print axioms YM.MassiveQCD.Play.Chamber.costProj
#print axioms YM.MassiveQCD.Play.Chamber.caveat
