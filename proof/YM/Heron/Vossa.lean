import YM.Heron.Lum
import YM.Heron.Lute
import YM.Heron.Laze
import YM.Heron.Pic
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad)
theorem stirDelta {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {f : E4 → X} (hf : Continuous f) (hc : HasCompactSupport f) (x : E4) :
    Tendsto (fun t => ∫ y : E4, Maxwell.Free.source t (y-x) • f y) (𝓝[>] (0:ℝ)) (𝓝 (f x)) := by
  have he t (ht : 0 < t) : (∫ y : E4, Maxwell.Free.source t (y-x) • f y) = ∫ y : E4, Maxwell.Free.source 1 y • f (x+t • y) := by
    rw [dilate_integral (fun y => Maxwell.Free.source t (y-x) • f y) x t ht, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_); simp only [add_sub_cancel_left,smul_smul, source_scale ht]
  obtain ⟨C,hC⟩ := hf.bounded_above_of_compact_support hc
  have hv : (∫ y : E4, Maxwell.Free.source 1 y • f x) = f x := by rw [integral_smul_const, source_profile.2,one_smul]
  refine Tendsto.congr' ?_ (show Tendsto (fun t : ℝ => ∫ y : E4, Maxwell.Free.source 1 y • f (x+t • y)) _ _ from ?_)
  · filter_upwards [self_mem_nhdsWithin] with t ht; exact (he t ht).symm
  rw [← hv]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖Maxwell.Free.source 1 y‖ * C) _ _
    (source_profile.1.norm.mul_const C)
  · refine Eventually.of_forall fun y => ?_
    have hg : Continuous (fun t : ℝ => Maxwell.Free.source 1 y • f (x+t • y)) := by fun_prop
    simpa using (hg.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  · exact Eventually.of_forall fun t => ((source_diff (by norm_num : (0:ℝ)<1)).continuous.smul
      (hf.comp (show Continuous fun y : E4 => x+t • y by fun_prop))).aestronglyMeasurable
  refine Eventually.of_forall fun t => Eventually.of_forall fun y => ?_
  change ‖Maxwell.Free.source 1 y • f (x+t • y)‖ ≤ ‖_‖ * _
  rw [norm_smul]; gcongr; exact hC _
variable (A:TinG)(hc:TrueC A)(p:E4)(D₀: Faces){U:Set E4}(hU:IsOpen U)(g:Spins)(v:Drive)(χ:E4→ℝ)(hw:Way A U g)(hv:Seam v)(he:tsupport χ⊆U)(hχ:ContDiff ℝ ∞ χ)(Hχ:HasCompactSupport χ)(hp:χ=ᶠ[𝓝 p] fun _=>1)
noncomputable def banner(A:TinG)(g:Spins)(v:Drive)(χ:E4→ℝ)(p:E4)(D₀:Faces)(t:ℝ):ℂ:= exportFlux (brook A (bz A p t D₀) g v) χ
local notation "q"=> banner A g v χ p D₀
include hw hv he hχ Hχ hp
lemma tea : Continuous q:=by
    unfold banner exportFlux; apply Continuous.neg; apply continuous_finsetSum; intro a _
    let P(t:ℝ):=bz A p t D₀; let U':= tsupport (grad a χ); have hK:= gradient_small Hχ a
    apply continuousOn_univ.mp (continuousOn_integral_of_compact_support hK ?_ ?_)
    · refine Continuous.continuousOn (continuous_iff_continuousAt.mpr fun z=> ?_); by_cases hz:z.2∈U'
      · have hs:=gradient_part χ a hz; have hP:p≠ z.2:=fun h=> collar hp (h ▸ hs); have Ht:= hw.live z.2 (he (tsupport_fderiv_subset ℝ hs)); have hp(i j:Axis):ContinuousAt (fun y:ℝ×E4=> streak A (P y.1) g i j y.2) z:=by
             apply ContinuousAt.sub; · exact ((dotL.continuous.continuousAt.comp (crisp A D₀ p z hP)).clm_apply ((cog A i).continuous.continuousAt.comp ((Maxwell.grad_smooth j Ht (m:=∞) (by simp)).continuousAt.comp continuousAt_snd)))
             exact ((dotL.continuous.continuousAt.comp (afoot A D₀ p j z hP)).clm_apply ((cog A i).continuous.continuousAt.comp (Ht.continuousAt.comp continuousAt_snd)))
        apply ((gradient_smooth hχ a).continuous.comp continuous_snd).continuousAt.smul; exact tendsto_finsetSum _ (fun b _=>(((hv.smooth b).continuous.comp continuous_snd).continuousAt (x:=z)).smul ((hp a b).add (hp b a)))
      apply continuousAt_const.congr (show (fun _ : ℝ×E4=> (0:ℂ))=ᶠ[𝓝 z] fun y=>grad a χ y.2 • brook A (bz _ _ y.1 D₀) g v a y.2 from ?_)
      filter_upwards [continuousAt_snd.preimage_mem_nhds ((isClosed_tsupport (grad a χ)).isOpen_compl.mem_nhds hz)] with y hy; rw[image_eq_zero_of_notMem_tsupport hy,zero_smul] -- hy type?
    intro t x _ hx; rw [image_eq_zero_of_notMem_tsupport hx,zero_smul]
include hc hU
lemma sourceP : q 0 = (-4:ℝ) • dotL D₀ (twistS A v g p):=by
    let L:= vale A v g χ D₀
    rw [← pays A hc p D₀ (he (enclosed p hp)) g v χ hw hv hp]; have ht:= loft A D₀ g v χ hw hv he hχ Hχ
    apply tendsto_nhds_unique ((tea A p D₀ g v χ hw hv he hχ Hχ hp).continuousAt (x:=0) |>.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
    apply (stirDelta ht.1.continuous ht.2 p).congr'; filter_upwards [self_mem_nhdsWithin] with t ht; exact (bridger A hc p t (show 0<t from ht) D₀ hU g v χ hw hv he hχ Hχ).symm
end YM.Heron
#print axioms YM.Heron.sourceP
