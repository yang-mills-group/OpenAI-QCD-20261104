import YM.Avian.Mile
/-! Every-component limit.Same volume. Off-shell map exact to physical S/A. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Jewels
open Function Lattice RG Source Wilson Filter Finset Topology
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper Tawny Cast Patria.Rolls Patria.Rolls.Attain Seals Pane BendR UV.Free KeysP Clifford
variable {C:Sequence}(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore 8)(H:Bore 10)(hT:Rubric sym B)(hH:Rubric sym H)(F:ℕ→PatchMix 8)(hψ:∀ᶠ i in atTop, OrderMix (C.A i) T sym B (i:=0) (F i)∧∃ W,Wager (C.A i) T H W 0)
variable (x:ℂ)(Q:RawTensor x 8)(hA:∀ i,(C.A i).Actual) (hR:Tendsto (fun i=> ↑((C.S.side (C.R i) 0).val):ℕ→ℝ) atTop atTop)(hI:∀ t b i, Lat.Invariant (B t b i))
variable (P:BudgetPoint)(n m:ℕ)(t a:ℝ)(hN:10 ≤ P.order)(hm:6≤ n)(hC:2 < m)(ht:0<t)(hh:3 ≤ P.power)(hQ:∀ᶠ i in atTop,∀ j k:Axis, Tutor 0 P (Canvas.foil ((C.A i).density 0) (path (C.A i) B (F i) x Q j k 0)) t n m a)
variable (w:ℕ→Axis→Axis→Label 10)(hw:∀ᶠ i in atTop,∀ j k:Axis,Tally T 0 (w i j k) ((C.A i).density 0) (trolley (C.A i) (vine (C.A i) B (F i) x Q j k) (shelV k) 0 0))
local notation "Ω"=> RawVec 10
set_option quotPrecheck false
local notation "Γ" i:arg=> ((C.S.side (C.R i) 0).val:ℝ)
section Capture
variable (D: ℕ → RawVec 10)
local notation "W"=> P.order
set_option maxHeartbeats 700000
include hw hQ hR hA hψ hN hm hh hC ht hI hH hT
private lemma viewP (h:∀ᶠ i in atTop,∀ j: Axis,(D i).val j=∑ a:Axis, w i a j) : Tendsto (fun i=> viewsL (D i)) atTop (𝓝 (viewsX x Q)):=by
     apply Tendsto.prodMk_nhds
     · let y:= obS x Q; change Tendsto (fun i=> obV (D i)) atTop (𝓝 y); apply tendsto_pi_nhds.mpr; intro a1; apply tendsto_pi_nhds.mpr; intro a2; apply tendsto_pi_nhds.mpr; intro i₁; apply tendsto_pi_nhds.mpr; intro i₂; let g i:=obV (D i) a1 a2 i₁ i₂; let p:=y a1 a2 i₁ i₂
       apply tendsto_iff_norm_sub_tendsto_zero.mpr
       apply squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) _ (g:=fun i=> 4* port a (C.S.side (C.R i) 0) t); swap
       · filter_upwards [hw,h,hQ,hψ] with i hi hg hp hv; exact shells _ T sym B hT (F i) hv.1 x Q (hA i) _ hi _ hg P n m t a hm hC ht hp a1 i₁ i₂ a2
       simpa only [Function.comp_apply, port,div_eq_mul_inv,mul_zero,zero_mul] using ((((tendsto_inv_atTop_zero.comp hR).const_mul 80).mul_const (a * (t^2)⁻¹)).const_mul 4) -- div_def
     change Tendsto (fun i=> gaugeQ (D i)) atTop (𝓝 (gaugeA x Q)); apply tendsto_pi_nhds.mpr; intro j; obtain ⟨s,hV,h₀⟩:= ask T j P hN hh; apply tendsto_iff_norm_sub_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) _ (g:=fun i=> 4*((Γ i)⁻¹*(s*a))); swap
     · filter_upwards [hw,h,hQ,hψ] with i hi hu hv hg -- h conflict
       exact h₀ _ _ _ hT (F i) hg.1 x Q (hA i) hI _ hi _ hu _ _ _ _ hv
     simpa only [Function.comp_apply,mul_zero,zero_mul] using (((tendsto_inv_atTop_zero.comp hR).mul_const (s*a)).const_mul 4)
private lemma boreP (h:∀ᶠ i in atTop,∀ j: Axis,(D i).val j=∑ a:Axis, w i a j): Tendsto (fun i=>lookQ (D i)) atTop (𝓝 0)∧Tendsto (fun i=>lookB (D i)) atTop (𝓝 0):=by
     obtain ⟨K,hK,hL⟩:= speedT T Gpick 0 1 P hh (by decide) ruby_pick.choose_spec -- order
     let S:= (4:ℝ)*(4*2^P.power*a/t^2) -- not power. define.
     let g(i:ℕ):= K*S*(Γ i)⁻¹; let f(i:ℕ):= costQ 2*tick (C.S.side (C.R i) 0)*S
     have he := (((tendsto_inv_atTop_zero.comp hR).const_mul K).const_mul S)
     have hv:Tendsto g atTop (𝓝 0):=by simp only[mul_zero] at he; refine he.congr fun i=>?_ ; unfold g; rw[Function.comp_apply]; ring
     have ht': Tendsto f atTop (𝓝 0):=by unfold f; simp_rw [tick,div_eq_mul_inv]; simpa only [Function.comp_apply,mul_zero,zero_mul] using ((((tendsto_inv_atTop_zero.comp hR).const_mul (2*Real.pi)).const_mul (costQ 2)).mul_const S)
     have hy:∀ᶠ i in atTop,∀ j a,‖lookQ (D i) j a‖ ≤ g i∧ ‖lookB (D i) j a‖ ≤ f i:=by
          filter_upwards [hw,h,hQ,hψ] with i hi hx hp hz j ⟨v,u⟩; obtain ⟨h1,h2⟩:= lookV _ T sym B hT (F i) hz.1 x Q (hA i) hI _ hi _ hx P n m t a hN hm hC ht hp hh j v u K hL; exact ⟨h1.trans_eq (by unfold g S; ring),h2.trans_eq (by unfold f S; ring)⟩
     constructor
     · apply tendsto_pi_nhds.mpr; intro j; apply tendsto_pi_nhds.mpr; intro a; exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (hy.mono fun i hi=>(hi j a).1) hv)
     apply tendsto_pi_nhds.mpr; intro j; apply tendsto_pi_nhds.mpr; intro a; exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (hy.mono fun i hi=>(hi j a).2) ht')
-- local continuity.S.Vol.L.Cover
lemma certifiedL :∃ d:RawVec 10,(viewsL d)=viewsX x Q∧lookQ d=0∧ lookB d=0 ∧∀ j:Axis, Tendsto (fun i=>∑ a:Axis,w i a j) atTop (𝓝 (d.val j)) :=by
     let y(i:ℕ)(j:Axis):= ∑ a:Axis,w i a j; have h:∀ᶠ i in atTop,(y i)∈RawVec 10:=by
          filter_upwards [hw,hψ] with i hi hx; obtain ⟨hv,W',hV⟩:=hx; apply vectorial _ T sym B hT H hH _ hV (hA _) _ hv x Q (y i) ?_; intro j
          suffices hf:Tally T 0 (y i j) ((C.A i).density 0) (castG (C.A i) B (F i) x Q j) by exact hf
          unfold castG divine; let f(a):= vine (C.A i) B (F i) x Q a j; let L:=(C.A i); let M:= ((C.A i).density 0); let V(f):= trolley L f (shelV j) 0 0
          have ht(q p: Cover→Insertion (C.S.side (C.R i) (C.N i)) 6) : V (q+p)=V q+V p:=treadM ..
          have hx(i':Axis): Tally T 0 (w i i' j) M (V (f i')):=hi ..
          unfold y; change Tally T _ _ _ (V (∑ a:Axis,f a)); simp_rw [Fin.sum_univ_four,ht]
          exact Needle.totalY _ _ _ _ _ _ _ (Needle.totalY _ _ _ _ _ _ _ (Needle.totalY _ _ _ _ _ _ _ (hx 0) (hx 1)) (hx 2)) (hx 3)
     let D(i:ℕ):RawVec 10:= if h:y i∈RawVec 10 then ⟨y i,h⟩ else 0; have hp:∀ᶠ i in atTop,∀ j:Axis,(D i).val j=y i j:=h.mono fun i hi=>by unfold D; rw [dif_pos hi]; exact fun _=>rfl
     have hv:= viewP T sym B H hT hH F hψ x Q hA hR hI P n m t a hN hm hC ht hh hQ w hw D hp
     obtain ⟨ha,hb⟩:= boreP T sym B H hT hH F hψ x Q hA hR hI P n m t a hN hm hC ht hh hQ w hw D hp
     let p:=(viewsX x Q,(0:Memory)); have hf:Tendsto (yearL∘D) atTop (𝓝 p):= hv.prodMk_nhds ha
     letI:FiniteDimensional ℂ ↥Ω:= FiniteDimensional.finiteDimensional_submodule (K:=ℂ) (V:=Axis→Label 10) Ω
     have hY:= LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr scansion); obtain ⟨v,hV'⟩:= hY.isClosed_range.mem_of_tendsto hf (Eventually.of_forall fun i=>Set.mem_range_self (f:=yearL) (D i))
     have htD: Tendsto D atTop (𝓝 v):= hY.isEmbedding.tendsto_nhds_iff.mpr (hV'.symm ▸ hf)
     refine ⟨v,congr_arg Prod.fst hV',congr_arg Prod.snd hV',tendsto_nhds_unique ((lookB.toContinuousLinearMap.continuous.tendsto _).comp htD) hb,fun i=>?_⟩
     exact ((continuous_apply i|>.comp continuous_subtype_val).continuousAt (x:=v)|>.tendsto.comp htD).congr' (hp.mono fun k hk=> hk i)
end Capture
end YM.Massive.Patria.Gall.Jewels
#print axioms YM.Massive.Patria.Gall.Jewels.certifiedL
