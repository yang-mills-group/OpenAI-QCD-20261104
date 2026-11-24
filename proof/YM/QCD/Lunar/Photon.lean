import YM.QCD.Lunar.Signal
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
namespace Ring0
noncomputable abbrev glow (P : BudgetPoint)(β:PlaqAxes)(G:Gauge)(V:Pot G c)(k:ℝ):= signal P G β V k/(c.val:ℝ)^4
structure PulseS (P:BudgetPoint)(β:PlaqAxes)(G:Gauge)(Y:Pot G c)(Z:ℝ)(D:ℝ)(t:ℝ):Prop where
    upT :0 < t
    fees (w:ℝ)(ht:w∈Set.Ioc 0 t):|glow P β G Y w - Z| ≤ D*w
variable {β:PlaqAxes}{H:Pot G c}{v X:ℝ}
lemma aro (p:PulseS P β G H v X t) : Tendsto (glow P β G H) (𝓝[>] (0:ℝ)) (𝓝 v):=by -- syntax H... decl
    have ht : Tendsto (fun y:ℝ=> X*y) (𝓝[>] (0:ℝ)) (𝓝 0):= Continuous.tendsto' (f:=fun y:ℝ=> X*y) (by fun_prop) 0 0 (mul_zero X)|>.mono_left nhdsWithin_le_nhds
    apply Metric.tendsto_nhds.mpr; intro ε he; filter_upwards [self_mem_nhdsWithin (a:= (0:ℝ)) (s:=Set.Ioi 0),nhdsWithin_le_nhds (ge_mem_nhds p.upT),ht.eventually (gt_mem_nhds he)] with x hx ht hV; exact lt_of_le_of_lt (p.fees x ⟨hx,ht⟩) hV
section all
variable (β:PlaqAxes)(T:G.Simple){I:Type*}
lemma horizonS {f:I→Pot G c}(hp:∀ U:Config G c, HasSum (fun i=>f i U) (H U))(V:Dir G c)(t:ℝ): HasSum (fun i=>sec V (f i) t) (sec V H t) := by
     have h := (((hp (pass V t)).sub (hp 1)).mul_left 2).mul_right (t^2)⁻¹; simpa only [sec,div_eq_mul_inv] using h
lemma convertG {f:I→ Pot G c}{A:Pot G c}(hp:∀ U:Config G c,HasSum (fun i=> f i U) (A U))(t:ℝ)(P:BudgetPoint): HasSum (fun i=> signal P G β (f i) t) (signal P G β A t):=by
     let S:=Site c
     let Z i:= rod G P (i:S) β
     let E : S→S→ Pot G c→ℝ:=fun i j V=> coord j i β.val.1^2*(1/(2*(P.threshold/2)^2)*call (Z i) (Z j) V t)
     change HasSum (fun k=> -1/2*(∑ i:S,∑ j:S,E i j (f k))) _
     have h (i j:S): HasSum (fun k=> E i j (f k)) (E i j A):= ((((horizonS hp (Z i+Z j) t).sub (horizonS hp (Z i) t)).sub (horizonS hp (Z j) t)).mul_left _).mul_left _
     exact (hasSum_sum fun i _=> hasSum_sum fun j _=>h i j).mul_left _ -- defeq
-- EN: normalized. Polynomial invoice.
lemma absoluteR (f:I→ℝ)(h:SumBudget (fun i=>|f i|) u) : Summable f ∧ |∑' i,f i| ≤ u:=⟨Summable.of_norm (show Summable (fun i=> ‖f i‖) from h.2.1),(norm_tsum_le_tsum_norm (show Summable (fun i=> ‖f i‖) from h.2.1)).trans h.2.2⟩
include T
variable {Z:ℝ}
set_option maxHeartbeats 500000 in
lemma crescent (P:BudgetPoint)(c:Side): ∃ t:ℝ,∀ (I:Type) (p:I→Pot G c)(s:I→ ℝ)(Y:I→RegularAddress c)(hc:∀ i,P.Regular (Y i).support (p i))(hp:SumBudget s Z) (hv:∀ i,P.supBounds (Y i).site (Y i).support (p i) (s i)) (K:Pot G c) (H:∀ U:Config G c, HasSum (fun i=> masked P.threshold (Y i).support (p i) U) (K U)),
     let dK:=∑' i, detectorK G β (p i)
     SumBudget (fun i=> |detectorK G β (p i)|) (meterP P c*Z) ∧ PulseS P β G K (dK/(c.val:ℝ)^4) (meterP P c*Z/(c.val:ℝ)^4) t :=by
      obtain ⟨t,he,hh⟩:= height T β P c
      refine ⟨t,fun I p s Y hc hp hv K H=>?_ ⟩; intro y; let f i:=detectorK G β (p i); let Q:= meterP P c; let A i:=masked P.threshold (Y i).support (p i)
      have h(i):=falsetto T β (hc i) (hv i) he hh
      have hU:0≤ Q:=by unfold Q meterP; positivity
      let C:ℝ:=c.val; have hD:0<C^4:=by unfold C; positivity
      have hx : SumBudget (fun i=> |f i|) (Q*Z):= Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_scale hU hp) (fun _=>abs_nonneg _) (fun i=>(h i).1) -- name
      refine ⟨hx,he,fun u hu=>?_⟩; have hh : HasSum f y:= (absoluteR f hx).1.hasSum
      have hm : SumBudget (fun i=> |signal P G β (A i) u-f i|) (Q*Z*u):=by
          have ht : 0≤ Q*u:=mul_nonneg hU hu.1.le
          rw [mul_right_comm]; apply Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_scale ht hp) (fun _=>abs_nonneg _) fun i=> ?_
          exact ((h i).2 u hu).trans_eq (mul_right_comm ..)
      have hf := convertG β (f:=A) H u P; have hY:= hf.sub hh; unfold glow; rw [← sub_div, abs_div, abs_of_pos hD, div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ hD.le; rw [← hY.tsum_eq]; exact (absoluteR _ hm).2
end all
end Ring0
end YM.QCD.Lunar
