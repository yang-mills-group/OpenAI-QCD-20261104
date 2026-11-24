import YM.Iceberg.Dew
set_option autoImplicit false
noncomputable section
namespace YM.Iceberg
open Function Filter Set
open scoped Topology BigOperators Classical
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X]
variable {I:Type*}[Fintype I](F: I→ℕ→X→ₗ[ℂ]ℂ)(L:I→ X→ₗ[ℂ]ℂ)(hF:∀ i p,Tendsto (fun k=>F i k p) atTop (𝓝 (L i p)))(hL:∀ x,(∀ i,L i x=0)→x=0)
include hF hL
lemma killU:∃ c:ℝ,0<c ∧ ∀ᶠ k in atTop,∀ u:X,‖u‖=1→∃ i:I,c ≤ ‖F i k u‖:=by
    by_contra! hx; have h(k:ℕ):∃ v:X, ∃ i:ℕ,k ≤ i∧‖v‖=1∧∀ j,‖F j i v‖ < ((k:ℝ)+1)⁻¹:=by
          obtain ⟨i,⟨v,hv,h'⟩,hk⟩:=(hx _ (show 0<((k:ℝ)+1)⁻¹ by positivity)).and_eventually (eventually_ge_atTop k)|>.exists; exact ⟨v,i,hk,hv,h'⟩
    choose v f hf hv hs using h
    letI :ProperSpace X:= FiniteDimensional.proper ℂ _
    obtain ⟨y,ht,g,hg,hv'⟩:= (isCompact_sphere (0:X) 1).tendsto_subseq (fun i=>Metric.mem_sphere.mpr ((dist_zero_right (v i)).trans (hv i)))
    have he : y≠0:=by intro h; rw[h] at ht; simpa using ht
    have hU:Tendsto f atTop atTop:= tendsto_atTop_mono hf tendsto_id
    refine he (hL y (fun i=>?_))
    apply tendsto_nhds_unique (follows_L (F i ∘ f ∘ g) (L i) (fun v=>(hF i v).comp (hU.comp hg.tendsto_atTop)) (v∘ g) y hv')
    have h: Tendsto (fun k:ℕ=>((k:ℝ)+1)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    exact squeeze_zero_norm (fun k=> (hs (g k) i).le) (h.comp hg.tendsto_atTop)
lemma sink (u:ℕ→X)(hu:∀ i,Tendsto (fun k=>F i k (u k)) atTop (𝓝 0)): Tendsto u atTop (𝓝 0):=by
    apply Metric.tendsto_nhds.mpr; intro ε he; obtain ⟨c,hc,h⟩:=killU F L hF hL
    filter_upwards [h,eventually_all.mpr fun i=>(hu i).eventually (Metric.ball_mem_nhds _ (mul_pos he hc))] with k hk ht
    rw[dist_zero_right]; by_cases hz:u k=0; · rw[hz,norm_zero]; exact he
    have hp :0<‖u k‖:=norm_pos_iff.mpr hz; let p:ℂ:=↑‖u k‖⁻¹; have hu:‖p‖= ‖u k‖⁻¹:=by unfold p; push_cast; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hp.le]
    obtain ⟨i,hi⟩:= hk (p • u k) (by rw [norm_smul,hu,inv_mul_cancel₀ hp.ne']); rw [map_smul,norm_smul,hu] at hi; specialize ht i; rw [dist_zero_right] at ht; refine lt_of_mul_lt_mul_left ?_ hc.le; exact lt_of_le_of_lt ((mul_comm c _).le.trans ((le_inv_mul_iff₀ hp).mp hi)) (lt_of_lt_of_le ht (mul_comm ε c).le)
lemma costW (u:ℕ→X)(v:X)(h:∀ i,Tendsto (fun k=>F i k (u k)) atTop (𝓝 (L i v))):Tendsto u atTop (𝓝 v):=by
    let Y(k:ℕ):=u k-v
    have ht:Tendsto Y atTop (𝓝 0):=sink F L hF hL Y fun i=>by simpa only [Y,map_sub,sub_self] using ((h i).sub (hF i v))
    simpa only [Y,sub_add_cancel,zero_add] using (ht.add_const v)
end YM.Iceberg
#print axioms YM.Iceberg.costW
