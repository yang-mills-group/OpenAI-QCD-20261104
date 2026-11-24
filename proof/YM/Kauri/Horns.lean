import YM.Kauri.Vibes
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice MeasureTheory QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open Module
open Ortho (plane Skew)
open scoped YM.Iceberg
noncomputable abbrev TTot:= bendP fun _=>1
noncomputable def feeF: BoxD →ₗ[ℂ] Free.Symbol 8:= pulseB.toBasis.constr ℂ fun i=> projection (TTot.val i)
lemma ele(i:Hea): feeF (pulseB i)=projection (TTot.val i):= pulseB.toBasis.constr_basis _ _ _
variable {σ:RawSym}(R:Roof σ)
lemma toast(s:EuPin) (x:BoxD): feeF (dues s x)= caravan R 8 s (feeF x):=by
      suffices hx : feeF ∘ₗ (dues s).toLinearMap= (caravan R 8 s).toLinearMap ∘ₗ feeF from DFunLike.congr_fun hx x; refine pulseB.toBasis.ext fun ⟨i,j⟩=> ?_; change feeF (troopL _ (pulseB.toBasis _))=_; rw [sol]; simp_rw [map_sum,map_smul]; change (∑ a:Axis,∑ b:Axis, (↑(s.coord.val a i*s.coord.val b j):ℂ) • feeF (pulseB (a,b)))= caravan R 8 s (feeF (pulseB (i,j))); simp_rw [ele]; exact (realA s i j σ R).symm
include R
lemma themes(g:Skew)(x:BoxD): feeF (stall g x)= rain g 8 (feeF x):=by
     have he:= chime g (tour g) R (feeF x); let L:= feeF.toContinuousLinearMap.restrictScalars ℝ; have hh:= L.hasFDerivAt.comp_hasDerivAt 0 (slipped g _ (tour g) x); apply HasDerivAt.unique hh; refine he.congr_of_eventuallyEq (Eventually.of_forall fun i=> toast R _ x)
omit R
noncomputable def bellT: ContDiffBump (0:ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩
noncomputable def flagX (x:E4):ℝ:= bellT (‖x‖^2)
local notation "Ff"=> flagX
noncomputable def topY:= points (![0,(1:ℝ) • basis timeAxis])
lemma rounds : topY∈conf 2:= DawnS.distinct 1 zero_lt_one
lemma rooms : Physics.Window topY flagX:=by
     have h : tsupport flagX ⊆ Metric.closedBall (0:E4) (1/2:ℝ) := by
           apply closure_minimal ?_ Metric.isClosed_closedBall; intro i hi; have hx: ‖i‖^2∈ tsupport (bellT:ℝ→ℝ):=subset_tsupport _ (show bellT _≠0 from hi); rw[bellT.tsupport_eq] at hx; simp only[Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,bellT,abs_of_nonneg (sq_nonneg ‖i‖)] at hx; simp only[Metric.mem_closedBall,dist_zero_right]; nlinarith [norm_nonneg i]
     refine ⟨bellT.contDiff.comp (contDiff_norm_sq ℝ), (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) h, ?_,?_⟩
     · have he:Continuous (fun x:E4=> ‖x‖^2):= continuous_norm.pow _; have hz : Tendsto (fun x:E4=>‖x‖^2) (𝓝 0) (𝓝 0):=by simpa using (he.continuousAt (x:=(0:E4))).tendsto
       exact hz.eventually bellT.eventuallyEq_one
     intro i hi; have hp:= h hi; fin_cases i; norm_num [topY] at hp
lemma w_move(g:Skew)(y:E4): ∑ a:Axis, Work.A05.weight flagX a (Work.A05.arm topY g a) y=0:=by
      let P:= fun t:ℝ=> Ortho.move (Ortho.oneParameter g t) y; have he:P 0=y:=by simp[P,oneParameter_zero]
      have ht: HasDerivAt P (M4.move g.val y) 0:=by
           have hv:= Work.A13.hasDerivAt_move g y 0; rw[oneParameter_zero,Ortho.move_one] at hv; exact hv
      have hh:= (rooms.1.differentiable (by simp) y).hasFDerivAt; have hp:fderiv ℝ flagX y (M4.move g.val y)=0:=by
           apply HasDerivAt.unique (f:=flagX ∘ P) (x:=(0:ℝ)); · exact (hh.comp_hasDerivAt_of_eq _ ht he.symm)
           refine (hasDerivAt_const (x:=(0:ℝ)) (flagX y)).congr_of_eventuallyEq (Eventually.of_forall fun i=>?_); simp[flagX,P, Ortho.move_norm]
      -- combine
      let v:= M4.move g.val y; have h(a:Axis):Work.A05.weight flagX a (Work.A05.arm topY g a) y=(↑(D (basis a) flagX y*v a):ℂ):=by
                      unfold Work.A05.weight Work.A05.arm; -- arm rfl?
                      simp [topY,v]
      simp_rw [h, ←Complex.ofReal_sum]; rw [show ∑ a:Axis,D (basis a) flagX y*v a=0 from ?_,Complex.ofReal_zero]; rw [show ∑ a:Axis,D (basis a) flagX y*v a=fderiv ℝ flagX y (∑ a:Axis,v a • basis a) from ?_,show ∑ a:Axis,v a • basis a=v from ?_]; exact hp
      · ext1 i; simp
      simp_rw [map_sum,map_smul]; apply Finset.sum_congr rfl; intro _ _; exact mul_comm ..
end YM.Kauri
#print axioms YM.Kauri.w_move
#print axioms YM.Kauri.themes
