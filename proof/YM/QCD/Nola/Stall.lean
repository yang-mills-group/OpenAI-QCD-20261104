import YM.QCD.Nola.Weather
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι κ A B:Type*} {n : Side} {m:ℕ} [Fintype A]{s t a χ δ v C H η b:ℝ}
open Kites Pads Creek.Ledge
-- Norm exact
noncomputable abbrev band (p:A→Site n)(x:Alg A)(t:ℝ)(m:ℕ):=∑ i:Finset A,grainH p x t m i
lemma bandPay (p:A→Site n)(x:Alg A)(t:ℝ)(ht:0<t)(D:Support n)(m:ℕ)(h:x∈region (alphabet (p:=p) D)): band p x t m ≤ ‖engine t A x‖ * tell D m:=by
     change _ ≤ load (fun _ : A=>t) x * _; rw [dry _ (fun _=>ht) x,sum_mul]; apply sum_le_sum; intro i _; rw [grainH,prod_const]
     by_cases hh : i ⊆ alphabet (p:=p) D
     · rw [mul_comm _ (‖coef i x‖)]; gcongr
       unfold tell; gcongr; apply reel_mono; intro j hj; obtain ⟨k,hk,rfl⟩:=mem_image.mp hj; exact (mem_filter.mp (hh hk)).2
     rw [ember x h i hh,norm_zero, zero_mul,mul_zero, zero_mul,zero_mul]
@[fun_prop] lemma bandC (p:A→Site n)(t:ℝ)(m:ℕ): Continuous fun x:Alg A=> band p x t m:=by unfold band grainH; fun_prop
lemma band_zero (p:A→Site n):band p (0:Alg A) t m=0:=by simp only [band,grainH,map_zero,norm_zero, zero_mul,sum_const_zero]
lemma band_add (p:A→Site n)(x y:Alg A)(hp:0<t):band p (x+y) t m≤ band p x t m+band p y t m:=by
       unfold band; rw [← sum_add_distrib]; apply sum_le_sum; intro i _; unfold grainH; rw [map_add, ← add_mul, ← add_mul]; gcongr; exacts [zero_le_one.trans (tell_one ..), norm_add_le ..]
lemma bandS (p:A→Site n)(Z : ι→ Alg A)(i:Finset ι)(hp:0<t):band p (∑ j ∈ i,Z j) t m ≤ ∑ j∈i, band p (Z j) t m:=by
   induction i using Finset.induction_on with
   | empty=> rw [sum_empty,sum_empty,band_zero]
   | insert i z hi ih=> rw [sum_insert hi,sum_insert hi]; exact (band_add _ _ _ hp).trans (add_le_add_right ih _)
lemma bandSerial (p:A→Site n)(Z:ι → Alg A)(X: Alg A)(hp:0<t)(hw:HasSum Z X)(h:SumBudget (fun i=>band p (Z i) t m) b): band p X t m≤ b:=by
     apply le_of_tendsto (x:=atTop) (f:=fun i:Finset ι=>band p (∑ j∈i,Z j) t m) ((bandC ..).continuousAt.tendsto.comp hw); exact Eventually.of_forall fun i=> (bandS p Z i hp).trans (budget_sum h _)
variable (p: Pairs A→Site n)(V:Matrix A A ℂ)(X:Patio (Pairs A))
lemma march (x:Site n)(he:0 < t)(hx:0 < χ)(h:s=Real.exp 2*t)(hi:soilH p X.val s m x ≤ δ): ∑ i:Peak (Pairs A),(if x∈poly p (.inl i) then scaleS p V X t χ m (.inl i)*currencyCard 2 (poly p (.inl i)) else 0) ≤ χ⁻¹*δ :=by
     subst s; let u:=Real.exp 2*t; let f (i:Finset (Pairs A)):=if x∈ edges p i then χ⁻¹*grainH p X.val u m i else 0; have H:0<u:=mul_pos (Real.exp_pos _) he; have hp:(∑ i: Finset (Pairs A), f i)≤ χ⁻¹*δ:=by
          apply le_trans _ (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hx.le)); unfold soilH; rw [mul_sum]; refine Finset.sum_le_sum fun i _=> ?_; unfold f; split <;> simp_all [u] -- edit
     refine le_trans ?_ ((budget_pull (fun i:Peak (Pairs A)=>i.val) Subtype.val_injective (show SumBudget f (χ⁻¹*δ) from ⟨fun i=>by unfold f; split; apply mul_nonneg (inv_nonneg.mpr hx.le) (grains p X.val H i); exact le_rfl,Summable.of_finite,by rw [tsum_fintype]; exact hp⟩)).2.2) -- compares tsum
     rw [tsum_fintype]; refine sum_le_sum fun i _=>?_ ; split
     next h=> change _≤ if x∈ edges p i.val then _ else _; rw [if_pos (show x∈ edges _ _ from h)]; exact recoup _ _ _ he rfl hx.le _
     next h=> unfold f; split; exact mul_nonneg (inv_pos.mpr hx).le (grains p _ H _); exact le_rfl
lemma facade (hs:∀ i,rayK p V m i ≤ b) (hz:0<t)(he:0<χ)(hk:s=Real.exp 2*t)(h:∀ i,soilH p X.val s m i ≤ δ)(hp: χ⁻¹*δ+t⁻¹^2*Real.exp 4*b≤ a) : Ac.HitCard (mist p X V).leaves (scaleS p V X t χ m) 2 a:=by
     intro x; refine ⟨fun i=>?_,Summable.of_finite,?_⟩; · dsimp only; split; exact mul_nonneg (scale_pos p V X he.le m 0 i) (Real.exp_pos _).le; exact le_rfl
     rw [tsum_fintype,Fintype.sum_sum_type]; exact le_trans (add_le_add (march p V X x hz he hk (h x)) (June p V X hs x)) hp -- universes
-- central result
lemma roiling (hs:∀ i,rayK p V m i ≤ b)(he:0<t)(hx:0<χ)(hH:χ≤1)(hk:s=Real.exp 2*t)(h:∀ i,soilH p X.val s m i ≤δ)(ha:a>0)(hw:a ≤ 1)(hr:degreePriceCard (Real.exp a-1) 1 ≤1/2)(hp: χ⁻¹*δ+t⁻¹^2*Real.exp 4*b≤ a)(hh:coef ∅ X.val=0): ∃ X':Patio (Pairs A), fade V (exp X.val) = exp (light _ X') ∧ band p (light _ X') t m ≤ (Fintype.card (Site n):ℝ)*(χ*(Real.exp a-1))*2 :=by
    let S:=mist p X V; let H':=logS (blocked S.unionK) S.unite; let B:= scaleS p V X t χ m; let G(i: Clusters S.Join):=termP (blocked S.unionK) (tyre t ∘ S.unite) i; let D:= fun i=>light _ (S.scroll i)
    have hi(i):taxS p V X t i*tell (S.leaves i) m ≤ (if i.isLeft then χ else 1)* B i:=by
                                                                                           unfold B scaleS; split
                                                                                           next H=> apply le_of_eq; simp only [← mul_assoc, mul_inv_cancel₀ hx.ne',one_mul]; rfl
                                                                                           next=> unfold S; rw [one_mul,one_mul]
    obtain ⟨hv,-,hX,hu,-⟩:= thrills S _ (tax_pos p V X) B (scale_pos p V X hx.le _ 0) hi hx hH he (fun _=> le_rfl) (twirl p V X t he) (facade p V X hs he hx hk h hp) ha hw hr (clearH p V X) (engineP V)
    have hY:HasSum D (light _ H'):= hv.mapL (light _|>.toLinearMap.toContinuousLinearMap)
    refine ⟨H',(dotted p V X hh).trans ((congr_arg _ hX.symm).trans (Cove.light_exp _)),bandSerial p D _ he hY (budget_mono hu (fun i=>sum_nonneg (fun a _=>grains p _ he a)) ?_)⟩
    intro i; exact (bandPay p _ t he _ _ (regionP S i)).trans_eq (by change ‖tyre t (S.scroll i)‖ * _=_; rw [scaled])
end YM.QCD.Nola
