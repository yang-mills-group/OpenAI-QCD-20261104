import YM.QCD.Hearth.Focus
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
namespace Ring0
open Cove StepData Stew Reggae Patron Lat Acre Rails Kites Push.AbsoluteSums Matrix
variable {I:Type} {U:Patron.Gem c k I}{u₀:Pot su c}{v M θ H K:ℝ}
open Collection
variable (β:PlaqAxes)
-- archive Wrap spending independent of anchor count.Constant precise aids alpha.Aux.PP 
open PhysicalNext.Repeat
lemma keepsPanel (P:BudgetPoint)(hi:0<a)(v:ℝ)(N:ℕ) : (4 ≤ c.val) → (meterP P c*Real.exp (-(1/4:ℝ)*tollV P.B c)* ((c.val:ℝ)^4*|v|)/(c.val:ℝ)^4 ≤1) → ∃ t W:ℝ,∀ (I:Type)(X:Patron.Gem c N I), Crossing X → Quartz X → Licence P 2 v a X →
     ∃ Y:ℝ, |Y| ≤ Φ P.B (-7/4) c ∧ PulseS P β su (gaugeF X P) Y W t:=by
   -- polynomial.Err K
   let f(c:Side):=sPer c; let w(c:Side) := f c^4*|v|; have hd:= P.threshold_pos
   let U:=100/P.threshold^2*|v|
   intro hc hT; change meterP P c*Real.exp _* w c/_ ≤_ at hT -- edit
   obtain ⟨t,h⟩:= crescent β simple (Z:=w c) P c -- order
   refine ⟨t,meterP P c*w c/(c.val:ℝ)^4,fun I X hx hΩ L=>?_⟩; obtain ⟨s,hs,hY⟩:= L.zone; let R i:= river c N ∘ X.view i
   have hX i:= spores _ _ _ (hY i) (hx.blank.gauge i) hi.le; have hp i:= (hY i).travel; have hm: (Fintype.card (Site c):ℝ)= (c.val:ℝ)^4:=by rw [site_card]; push_cast; rfl
   have hv: (Fintype.card (Site c):ℝ)*v≤ w c:=by rw [hm]; exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
   have hS: SumBudget s (w c):= budget_loosen (Stem.mast X s hs hp (by norm_num)) hv
   have hh0(i j): (river c N) (letters X P.threshold i j)=masked P.threshold (X.addr j).support (R j) i:=by
       unfold letters; by_cases h:Healthy P.threshold (X.addr j).support i
       · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl
       rw [masked_ne _ _ _ _ h,map_zero, masked_ne _ _ _ _ h]
   have hP(i): HasSum (fun j=>masked P.threshold (X.addr j).support (R j) i) (gaugeF X P i):= ((river c N).hasSum (permits X L hi (by norm_num) i).hasSum).congr_fun fun j=> (hh0 i j).symm -- L cleared
   obtain ⟨hC,hW⟩:=h I R s X.addr (fun i=>(hX i).1) hS (fun i=>(hX i).2) _ hP; refine ⟨_,?_ ,hW⟩
   let q i:= detectorK su β (R i); let bad i:=¬Nonwrapping (X.addr i).support (X.addr i).site; let g i:= if bad i then s i else 0
   have hz : ∀ i, ¬bad i → q i=0:=by
        intro i hi; have hh : Nonwrapping (X.addr i).support (X.addr i).site:=of_not_not hi
        rw [show q i= coeff (R i) _ _ _ from phase simple (hX i).1 β hc hh]
        exact hΩ.van i hh ((wedge β (spike su)).field _) ((wedge β (spike su)).field _) ((LinearJet.isAffine _).mpr ⟨_,rfl⟩) ((LinearJet.isAffine _).mpr ⟨_,rfl⟩)
   -- anchored extraction
   let D:= Φ P.B (-2) c; have hg : SumBudget g (D*(w c)):=by
       have hx: Footprint.Anchored (fun i=>(X.addr i).site) g (fun i=>coverNumber P.B (X.addr i).support) 0 (D*v):=by
           intro i; apply budget_mono (budget_scale (Real.exp_pos _).le (hs i))
           · intro j; split; exact mul_nonneg (ite_nonneg (hp j) le_rfl) (Real.exp_pos _).le; exact le_rfl
           intro j; split
           next hJ=> dsimp only; unfold g; split
                     next hB=> rw [mul_left_comm,← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hp _); have hh:= Nat.cast_le (α:=ℝ).mpr (toll_top hB (X.addr j).anchor P.B); linarith
                     next hB=> have h':= hp j; rw [zero_mul]; positivity
           next hJ=> rw [mul_zero]
       refine budget_loosen (Stem.mast X _ hx (fun i=>ite_nonneg (hp i) le_rfl) le_rfl) ?_; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
   have hk : SumBudget (fun i=>|q i|) (meterP P c*(D*w c)):=by
       obtain ⟨t,he,ht⟩:=height simple β P c
       have hh:0 ≤ meterP P c:=by unfold meterP; positivity
       apply budget_mono (budget_scale hh hg) (fun _=>abs_nonneg _)
       intro i; unfold g; split
       · exact (falsetto simple β (hX i).1 (hX i).2 he ht).1
       next h=> rw [hz i h,abs_zero,mul_zero]
   rw [abs_div,abs_of_nonneg (show 0≤(c.val:ℝ)^4 from (by positivity))]; apply le_trans (div_le_div_of_nonneg_right (absoluteR q hk|>.2) (by positivity :0≤(c.val:ℝ)^4))
   apply le_trans _ (mul_le_mul_of_nonneg_right hT (Real.exp_pos (-(7/4:ℝ)*tollV P.B c)).le|>.trans_eq (one_mul _|>.trans (by unfold Φ; ring_nf))) -- last mismatched goal hT product else
   rw [div_mul_eq_mul_div]; unfold D Φ; apply le_of_eq; rw [show -(2:ℝ)* (tollV P.B c:ℝ) = -(1/4:ℝ)*(tollV P.B c:ℝ)+ -(7/4:ℝ)* (tollV P.B c:ℝ) by ring, Real.exp_add]; ring
end Ring0
end YM.QCD.Lunar
