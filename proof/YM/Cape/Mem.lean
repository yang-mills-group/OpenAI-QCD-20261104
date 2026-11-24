import YM.Cape.Meg
/-!
# Exact rebox earnings, for authentic Hearth rotations
Booster stays per-label in the satellite field. Top tile requires bounded scatter.Halo.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch Creek SC
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I]
variable (p:I→Site c)(q:I→Bool) (F: Film c N I D)(M: Patron.Rail c N U) (E: Reel c N I J)
variable {t v α s h u κ a A b m:ℝ} (X:Lake (c:=c) (I:=I) (J:=J) R t)
local notation "K"=> Keys c N
local notation "Xk"=> Ribbon.Spine I
local notation "L₀"=> brightP E X
local notation "W"=> reelShot E X
local notation "Kᴿ"=> unitR E X
variable {ξ:J→ℝ}{u':R→ℝ} {n:ℕ} (hz:SC.Valve E p q v t n α s ξ)(hp:X.Pillar p E)
include hz hp
lemma windmill (hv:∀ i,1≤ξ i)(hα:0≤α)(ht:1≤v)(i:R)(V:Grid c): Tablet.credits v (riseP E X i V) ≤ s:=by
   obtain ⟨k,hk,hΩ⟩:= hz.back
   obtain ⟨z,hZ⟩:= hp.zU i; let H:= Gate X (.some i); let f (j:H):= Reel.mist E t j.val V
   have hL(j:H):p z∈ (E.addr j.val).support:= hz.book.stamp _ (mem_image_of_mem _ ((hp.tapes _ _ j.2).symm ▸ hZ))
   have hg:SumBudget (fun i:H=>k i.val) s:=by
      let a:=(budget_pull (fun i:H=>i.val) Subtype.val_injective (hΩ (p z))); have hc i:0≤k i:=(Creek.load_nn ..).trans (hk i V); refine budget_mono a (fun i=> hc _) (fun i=>?_); rw [if_pos (hL i)]; exact (le_mul_of_one_le_left (hc i.val) (hv _)).trans (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans (hv _)) (hc i.val)) (Real.one_le_exp (mul_nonneg hα (Nat.cast_nonneg _))))
   let Φ:=Ribbon.banknote N p v; let L:= (token c (ample N I) v).comp (Φ.toLinearMap.toContinuousLinearMap.restrictScalars ℝ)
   have hf := flyer p q E hz hα hv ht; have hQ: Summable f:= (hf V).comp_injective Subtype.val_injective
   have hx:= zero_lt_one.trans_le ht; rw [← token_bill p q _ (lighthouse p q E hz.book X hp hf i V).1 hx]; change ‖L (∑' j,f j)‖≤ _ ; refine ((L.hasSum hQ.hasSum).norm_le_of_bounded hg.2.1.hasSum ?_).trans hg.2.2; exact fun j=> (token_bill p q (Reel.mist E t j.val V) (upM p q E hz.book j.val V).1 hx).trans_le (hk j.val V)
omit hp
lemma coldClime : SC.Valve W p q v t n α s (fun j=> ξ j.val):=by
   refine ⟨chocolate p q E hz.book X,?_⟩; obtain ⟨f,hf,hx⟩:= hz.back; exact ⟨fun j=>f j.val,fun j U=> hf j.val U,fun i=>budget_pull (fun i:Gate X none=>i.val) Subtype.val_injective (hx i)⟩
omit hz
lemma mixH (Y:Reel c N I R)(hz:SC.Valve E p q v t n α s ξ)(hp:SC.Valve Y p q v t n α b u'):SC.Valve (plusR E Y) p q v t n α (s+b) (Sum.elim ξ u'):=by
    refine ⟨powerV p q E hz.book Y hp.book,?_⟩; obtain ⟨f,hf,hΩ⟩:=hz.back; obtain ⟨F,hF,hP⟩:=hp.back
    refine ⟨Sum.elim f F, (?_:∀ j V,_), ?_⟩
    · rintro (i|i); exact hf _; exact hF _
    convert Labels.together _ _ _ hΩ hP using 1; all_goals funext i; cases i<;>rfl
-- card scatter via Fires p.M.W.Health. Geometry input.Type.C
lemma glebe {m₁ m₂ m₃:ℕ}(Q:R→Support c)(a₁:R→ I)(hr:∀ i,Q i⊆ halo m₁ {p (a₁ i)})(h:Fires p m₂)(he:∀ i (E:Finset R),(∀ j∈E,a₁ j=i)→ E.card≤ m₃):∀ (i:Site c)(U:Finset R),(∀ j∈U,i∈Q j)→ U.card ≤ (m₁+m₁+1)^4*m₂*m₃:=by -- infer bind
   intro i U hQ; let T:= (U.image a₁); let L:= halo m₁ {i}; have hU(j)(hj:j∈U):p (a₁ j)∈L:=by
       obtain ⟨z,hz,hv⟩:= halo_spec.mp (hr j (hQ j hj)); obtain rfl:=Finset.mem_singleton.mp hz; exact halo_spec.mpr ⟨_,mem_singleton_self _,separation_comm (p (a₁ j)) i ▸ hv⟩
   let f:=(T.image p); let z i:=Finset.univ.filter (fun j=>p j=i)
   have hp:T.card≤ L.card*m₂:=by
      have ht:T⊆L.biUnion z:=fun i hi=>by obtain ⟨x,hx,rfl⟩:=mem_image.mp hi; exact mem_biUnion.mpr ⟨_,hU x hx,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
      exact (card_le_card ht).trans ((card_biUnion_le ..).trans ((sum_le_sum fun i _=>h _).trans_eq (by rw [sum_const]; rfl)))
   let k r:=U.filter fun j=> a₁ j=r; have ht : U⊆ T.biUnion k:=fun i hi=>mem_biUnion.mpr ⟨_,mem_image_of_mem _ hi, mem_filter.mpr ⟨hi,rfl⟩⟩
   apply (card_le_card ht).trans; refine (card_biUnion_le ..).trans ((sum_le_sum fun i _=> he i (k i) (fun j hi=> (mem_filter.mp hi).2)).trans ?_); rw [sum_const]; apply Nat.mul_le_mul_right m₃; apply hp.trans; have hz:=Corona.halo_size {i} m₁; simp at hz; exact Nat.mul_le_mul_right m₂ hz
lemma cotton (n k :ℕ)(Q:R→Support c)(M N:ℕ)(w:ℝ)(hw:0≤w)(ha:0≤α)(hx:∀ i,coverNumber n (Q i) ≤ M)(hC:∀ (i:Site c)(Y:Finset R),(∀ j∈Y,i∈Q j)→Y.card≤ N): Ac.Hit Q n (fun _=>w) α (N*w*Real.exp (α*M)) :=by
    intro i; refine budget_of_sum (fun j=>ite_nonneg (mul_nonneg hw (Real.exp_pos _).le) le_rfl) fun Y=>?_; rw [← sum_filter]; let Z:= Y.filter fun j=> i∈Q j; have hh:=hC i Z (fun j hj=>(mem_filter.mp hj).2)
    apply (sum_le_sum (g:=fun _=>w*Real.exp (α*M)) ?_).trans
    · rw [sum_const,nsmul_eq_mul, ←mul_assoc]; gcongr
    intro j _; gcongr; exact hx _
include hz hp
lemma towers (M B:ℕ)(hv:∀ i,1≤ξ i)(hα:0≤α)(ht:1≤v)(ha:0≤a)(hx:∀ i,coverNumber n (X.addr i).support ≤ M)(hC:∀ (i:Site c)(Y:Finset R),(∀ j∈Y,i∈(X.addr j).support)→Y.card≤ B): 0 ≤ s ∧ (∀ i V, Stitch.Tablet.credits v (riseP E X i V) ≤ s) ∧ (∀ i V,Stitch.Tablet.credits v (Reel.mist (brightP E X) t i V)≤ s) ∧ (∀ i V, Stitch.Tablet.credits v ((lured E X).wick i V)≤ wig (fun _=>Real.log (1+s)) i) ∧ Ac.Hit (lured E X).spot n (fun _=>Real.log (1+s)) a (B*(Real.log (1+s))*Real.exp (a*M)) ∧ Ac.Hit (fun i=> ((brightP E X).addr i).support) n (fun _=>s) a (B*s*Real.exp (a*M)) :=by
    have hg:=budget_nonneg (hz.back.choose_spec.2 (0:Site c)); have h:= windmill p q E X hz hp hv hα ht; let f i:=(X.addr i).support; have hk : 0<1+s:=by linarith
    refine ⟨hg,h,?_,?_, cotton n 0 _ M B _ (Real.log_nonneg (by linarith)) ha hx hC,cotton n 0 _ M B s hg ha hx hC⟩
    · intro i V; change Tablet.credits v (masked t (f i) _ V) ≤ _; by_cases hv:Healthy t (f i) V; rw [masked_eq _ _ _ _ hv]; exact h i V
      rw [masked_ne _ _ _ _ hv]; unfold Tablet.credits; rw [map_zero,Cove.load_zero]; exact hg
    intro i V; rw [show wig (fun _=>Real.log (1+s)) i=s by unfold wig; rw [Real.exp_log hk]; ring]; change Tablet.credits v (_-masked t (f i) _ V) ≤ _; by_cases hv:Healthy t (f i) V; swap; · rw [masked_ne _ _ _ _ hv,sub_zero]; exact h i V
    rw [masked_eq _ _ _ _ hv]; change Tablet.credits v (riseP E X i V-riseP E X i V) ≤ _; unfold Tablet.credits; rw [sub_self,map_zero,Cove.load_zero]; exact hg
-- customizable weakening
lemma receiptsR [Countable J] (hv:∀ i,1≤ξ i)(hα:0≤α)(ht:1≤v)(hx:∀ i V, Tablet.credits v (Reel.mist L₀ t i V) ≤ u' i)(hX: Ac.Hit (fun i=> (X.addr i).support) n u' α b): Valve Kᴿ p q v t n α (b+s) (Sum.elim (fun _=>1) (fun i=>ξ i.val)):=by
    refine mixH p q L₀ W ⟨reading p q E hz.book X hp (flyer p q E hz hα hv ht),u',hx,?_⟩ (coldClime p q E X hz); simpa only [one_mul] -- maybe uses hX? 
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.towers
