import YM.Heron.Beads
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad away open_away)
open Arise.Range
variable (A:TinG)(p:E4)(D₀: Faces)(g:Spins)(v:Drive)(χ:E4→ℝ) (L:List Axis)(s:ℝ)(a b j:Axis)
noncomputable def arcT(p:E4)(a:Axis)(t:ℝ):E4:= p+t • basis a
local notation "X"=> arcT p j
local notation "Z"=> pose A D₀
local notation "R"=> dotL
lemma jetX : HasDerivAt X (basis j) s:=by apply HasDerivAt.congr_deriv (((hasDerivAt_id' s).smul_const (basis j)).const_add p); simp
variable (x:E4)(h:arcT p j s≠x)
include h
lemma jazz : HasDerivAt (fun t=>Z L (X t) x) (Z (j::L) (X s) x) s := by
    let f:= hull A D₀; let z:= X s-x; have hp:z≠0:=sub_ne_zero.mpr h
    exact ((balla L f _ open_away (fun y h=> hotH A D₀ y h) _ hp).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s ((jetX p s j).sub_const x)
lemma flour : HasDerivAt (fun t=> grad a (Z L (X t)) x) (grad a (Z (j::L) (X s)) x) s:=by
    rw[loveK A D₀ _ _ h]; have he := (jazz A p D₀ (a::L) s j x h).neg
    have ht: Z (a::j::L) (X s) x= Z (j::a::L) (X s) x:= commute_a open_away _ (fun y h=> hotH A D₀ y h) _ _ (List.Perm.swap j a L) (X s-x) (sub_ne_zero.mpr h); rw[ht];
    apply he.congr_of_eventuallyEq; filter_upwards [(jetX p s j).continuousAt.eventually_ne h] with t h; exact loveK A D₀ _ _ h L a
lemma cork :HasDerivAt (fun t=> streak A (Z L (X t)) g a b x) (streak A (Z (j::L) (X s)) g a b x) s:=by
     -- linear with f
     let F:= dotL.flip (cog A a (Maxwell.grad b g x)); let G:= dotL.flip (cog A a (g x)); exact (F.hasFDerivAt.comp_hasDerivAt s (jazz A p D₀ L s j x h)).sub (G.hasFDerivAt.comp_hasDerivAt s (flour A p D₀ L s b j x h)) -- with args
lemma bliss : HasDerivAt (fun t=> brook A (Z L (X t)) g v a x) (brook A (Z (j::L) (X s)) g v a x) s:= by
      unfold brook; refine HasDerivAt.fun_sum fun b _=>?_ ; exact ((cork A p D₀ g L s a b j x h).add (cork A p D₀ g L s b a j x h)).const_smul (v b x)
omit h
variable {hv:Seam v}{U:Set E4}(he:Way A U g)(hU:tsupport χ⊆ U)(hχ:ContDiff ℝ ∞ χ)(Hχ:HasCompactSupport χ)(hw:χ=ᶠ[𝓝 p] fun _=>1)
lemma mood(z:ℝ×E4)(hz:X z.1≠z.2) : ContinuousAt (fun u:ℝ×E4=> Z L (X u.1) u.2) z:= (balla L (hull A D₀) _ open_away (fun y h=>hotH _ _ _ h) _ (sub_ne_zero.mpr hz)).continuousAt.comp (x:=z) (f:=fun w:ℝ×E4=> X w.1-w.2) (((jetX p _ j).continuousAt.comp continuousAt_fst).sub continuousAt_snd)
lemma porch (z:ℝ×E4)(hz:X z.1≠z.2)(hg: ContDiffAt ℝ ∞ g z.2):ContinuousAt (fun w:ℝ×E4=>streak A (Z L (X w.1)) g a b w.2) z:=by
     have he: ContinuousAt (fun w:ℝ×E4=> grad b (Z L (X w.1)) w.2) z:=by
          refine ((mood A p D₀ _ j z hz).neg).congr (f:= fun w:ℝ×E4=> - Z (b::L) (X w.1) w.2) ?_
          filter_upwards [(show ∀ᶠ w:ℝ×E4 in 𝓝 z, X w.1 ≠ w.2 from ((((show ContinuousAt (fun w:ℝ×E4=> X w.1) z from (jetX p z.1 j).continuousAt.comp continuousAt_fst)).ne_iff_eventually_ne (continuousAt_snd)).mp hz))] with w hw; exact (loveK _ _ _ _ hw _ _).symm
     apply ContinuousAt.sub; · exact (dotL.continuous.continuousAt.comp (mood A p D₀ L j z hz)).clm_apply (((cog A a).continuous.continuousAt.comp (Maxwell.grad_smooth b (m:=∞) hg (by simp) |>.continuousAt)).comp continuousAt_snd)
     exact (dotL.continuous.continuousAt.comp he).clm_apply (((cog A a).continuous.continuousAt.comp hg.continuousAt).comp continuousAt_snd)
include he hU hv hχ Hχ hw
lemma bon : Integrable fun y:E4=> grad a χ y • brook A (Z L p) g v a y := shell_cost hχ Hχ (fun y h=> (bow _ _ g _ _ _ hv (nicePose A D₀ p y (fun t=> collar hw (t ▸ h)) L) (he.live _ (hU (tsupport_fderiv_subset ℝ h)))).continuousAt) a
lemma lineage : HasDerivAt (fun t=> exportFlux (brook A (Z L (X t)) g v) χ) (exportFlux (brook A (Z (j::L) p) g v) χ) 0:=by
     unfold exportFlux; apply HasDerivAt.neg; apply HasDerivAt.fun_sum; intro a _
     have hx : X 0=p:=by simp [arcT];
     let V:=tsupport (fderiv ℝ χ); have hK:IsCompact V:=Hχ.fderiv _; have ht: ∀ᶠ t in 𝓝 (0:ℝ), χ=ᶠ[𝓝 (X t)] fun _=>1 := (show Tendsto X (𝓝 0) (𝓝 p) from (show Tendsto X (𝓝 0) (𝓝 p) from (by have hm:Tendsto X (𝓝 0) (𝓝 (X 0)):=(jetX p 0 j).continuousAt; rwa [hx] at hm))) hw.eventuallyEq_nhds
     obtain ⟨r,hr,hr'⟩ := Metric.nhds_basis_closedBall.mem_iff.mp ht
     let M:= Metric.closedBall (0:ℝ) r
     have ha:M∈𝓝 (0:ℝ):= Metric.closedBall_mem_nhds _ hr
     let P (l: List Axis)(t :ℝ)(y:E4):= grad a χ y • brook A (Z l (X t)) g v a y; let q:= j::L; have Ht(l:List Axis) {t}(ht:t∈M): Integrable (P l t) := bon A (X t) D₀ g v χ _ a he hU hχ Hχ (hr' ht) (hv:=hv)
     have sep {t} (ht:t∈M){y}(hy:y∈V):X t≠ y:=fun he=> collar (hr' ht) (he ▸ hy)
     have hg: ContinuousOn (fun z:ℝ × E4=> P q z.1 z.2) (M ×ˢ V):=by
          intro z hz; obtain ⟨ht, hy⟩:= hz; have hp:= he.live z.2 (hU (tsupport_fderiv_subset ℝ hy)); apply ContinuousAt.continuousWithinAt; apply ((gradient_smooth hχ a).continuous.comp continuous_snd).continuousAt.smul
          exact tendsto_finsetSum _ fun b _=> (((hv.smooth b).continuous.comp continuous_snd).continuousAt (x:=z)).smul ((porch A p D₀ g _ a b j z (sep ht hy) hp).add (porch A p D₀ g _ b a j z (sep ht hy) hp))
     obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:ℝ) r).prod hK).exists_bound_of_continuousOn hg
     let B:= V.indicator fun _=> C
     have he : HasDerivAt (fun t : ℝ => ∫ y : E4, P L t y) (∫ y : E4, P q 0 y) 0 :=
       (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := P q) (bound := B) ha
         (Eventually.mono ha fun t ht => (Ht L ht).1) (Ht L (mem_of_mem_nhds ha))
         (Ht q (mem_of_mem_nhds ha)).1 ?_ ((continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet) ?_).2
     · simp only [P,hx,q] at he; exact he
     · refine Eventually.of_forall fun y t ht => ?_
       by_cases hy : y ∈ V
       · rw [show B y = C from indicator_of_mem hy _]; exact hC (t,y) ⟨ht,hy⟩
       have hh : grad a χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (gradient_part χ a h)
       simp [B,P,hy,hh]
     refine Eventually.of_forall fun y t ht => ?_
     by_cases hy : y ∈ V
     · exact (bliss A p D₀ g v L t a j y (sep ht hy)).const_smul (grad a χ y)
     have hh : grad a χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (gradient_part χ a h)
     simpa only [P,hh,zero_smul] using! hasDerivAt_const t (0:ℂ)
end YM.Heron
#print axioms YM.Heron.lineage
