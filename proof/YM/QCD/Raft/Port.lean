import YM.QCD.Raft.Still

/-! # identity of jets from actual blocked calculation at pure action graph. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Flume Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v r a:ℝ}{c f:Side}
lemma det_blocks (A:Sheet f)(B: Rail c f) (H:Sheet f)(he : H=A+Bᴴ * B)(hp : IsUnit H.det): A.det= H.det*(1-B*H⁻¹*Bᴴ).det:=by
  letI : Invertible H:=H.invertibleOfIsUnitDet hp
  have ht := det_fromBlocks₁₁ H Bᴴ B (1:Sheet c)
  rw [Matrix.invOf_eq_nonsing_inv,Matrix.det_fromBlocks_one₂₂,show H-Bᴴ * B=A from (by rw [he]; abel)] at ht; exact ht -- inspect
lemma sessionD {P Q: Cnr c → Sheet c}(h: Tender P Q 3):Duet P Q:=by
  obtain ⟨h,hL,hR⟩:= h
  have ht i (he:i<3): iteratedFDeriv ℝ i P 0=iteratedFDeriv ℝ i Q 0:=by have hm:= h i he; rw [iteratedFDeriv_sub_apply (hL.of_le le_top) (hR.of_le le_top)] at hm; exact sub_eq_zero.mp hm
  refine ⟨hL,hR,?_,fun v=>?_,fun u v=>?_⟩
  · have H:=DFunLike.congr_fun (ht 0 (by omega)) ![]; simpa using H -- simp risk
  · have H:=DFunLike.congr_fun (ht 1 (by omega)) ![v]; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply] at H; exact H
  rw [iter _ _ hL,iter _ _ hR,ht 2 (by omega)]
variable (P:Plan j)(L:Plan k)(V:Back E K j k p u v) {A: On}{B:On}
lemma warrant (i:ℕ)(h:Tender (V.charge P L A i) (castF (B _)) 3):
    Duet (pulseShift V.port P A i) (caravan L V.fly.land B _ ∘ input su (V.chain.n i)):= by
  obtain ⟨r,c,hp,hc,H⟩:= lumber L
  have he:= H (V.chain.n i) V.fly.land
  let Q:= fun x:Cnr (V.chain.n i)=>wood L 0 V.fly.land (input su _ x)
  have hp : ContDiffAt ℝ ω Q 0:=matrix_g fun j k=>(he j k).host
  have hx: V.charge P L A i= pulseShift V.port P A i-Q:=rfl
  have hh:= (Duet.together hp EventuallyEq.rfl).add (sessionD h)
  rw [hx,add_comm Q,sub_add_cancel] at hh; exact hh
-- chart witness geometry
lemma lecture (i)(R:Avenue V η Ω Θ): ∃ X:Cnr (V.chain.n i)→ Cnr (high V.fly V.chain i), X 0=0 ∧ ContDiffAt ℝ ω X 0 ∧ ((fun x=>(encamp (V.port.forest i) (V.port.u i) x).1)=ᶠ[𝓝 0] input su _ ∘ X) ∧ ∀ x, blade x X 0= Garden.rise (V.port.forest i) R.T x:=by
  let F:=V.port.forest i; let L:= arm su (V.chain.n i) 1; let K:= arm su (high V.fly V.chain i) 1; let Q:=chartOf F (V.port.u i); let H:= K.symm ∘ Q ∘ L
  have hu:= V.port.critical i; have hQ: Q 0=0:=by unfold Q chartOf; rw [hu.1]; exact congr_arg Prod.snd (Work.F03.inclusion_zero ..)
  have hp : ContDiffAt ℝ ω Q (L 0):= L.map_zero.symm ▸ chart_jet (V.port.u i) hu.2.1 hu.1
  have hx: H 0=0:=by unfold H; simp only [Function.comp_apply,map_zero,hQ]
  let G(x:Cnr (V.chain.n i)) := (L x,V.port.u i (L x))
  have hg:ContDiffAt ℝ ω G 0:= L.contDiff.contDiffAt.prodMk ((show ContDiffAt ℝ ω (V.port.u i) (L 0) by rw [map_zero]; exact hu.2.1).comp (f:=L) 0 L.contDiff.contDiffAt)
  have hf:G 0=0:=by unfold G; rw [map_zero,hu.1]; rfl
  have hM:= hp.comp (f:=L) 0 L.contDiff.contDiffAt
  refine ⟨H,hx,K.symm.contDiff.contDiffAt.comp _ hM,?_,fun x=>?_⟩
  · filter_upwards [(show Tendsto G (𝓝 0) (𝓝 0) from hf ▸ hg.continuousAt.tendsto).eventually (Work.F03.inclusion_works (G:=su) F)] with x Hx
    rw [Function.comp_apply,input,show arm su _ 1 (H x)= Q (L x) from K.apply_symm_apply _]; exact Hx.symm
  unfold blade H Garden.rise
  rw [fderiv_comp _ K.symm.differentiableAt (hM.differentiableAt (by simp)),ContinuousLinearMap.comp_apply,fderiv_comp _ (hp.differentiableAt (by simp)) L.differentiableAt,ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv,ContinuousLinearEquiv.fderiv,map_zero]; rw [show fderiv ℝ Q 0 (L.toContinuousLinearMap x)=_ from chart_tangent (V.port.u i) hu (R.sworn i) (L x)]; rfl
lemma tree_toll (i)(R:Avenue V η Ω Θ)(ha:Vital A)(hb:Vital B)(h:Tender (V.charge P L A i) (castF (B _)) 3)(hu:ContDiffAt ℝ ω (purchaseG V P A i) 0) (x:Cnr (V.chain.n i)) :
    let z:= Garden.rise (V.port.forest i) R.T x
    Jacobi.mixed z z (rollG P V.fly.wing A _) 0=Jacobi.mixed x x (purchaseG V P A i) 0 + Jacobi.mixed x x (rollG L V.fly.land B _) 0:=by
  intro z
  let n:= V.chain.n i; let f:=localG V i; let Q(y):=(encamp (V.port.forest i) (V.port.u i) y).1
  have ht:=V.port.critical i; have hQ : Q 0=1:= by unfold Q; rw [encamp_zero ht]; rfl
  obtain ⟨W,hW,hF,hV,hx⟩:= lecture V i R
  let Z:= caravan L V.fly.land B n ∘ input su n; let S:=pulseShift V.port P A i
  have hs: Duet S Z:=warrant P L V i h
  have H: IsUnit (Z 0).det:=by unfold Z; rw [Function.comp_apply,input_zero,(car_origin L V.fly.land B n hb).1]; exact (car_origin L V.fly.land B n hb).2 -- syntax
  have hS:IsUnit (S 0).det:=hs.meet ▸ H -- inspect
  have hh : rollG P V.fly.wing A f ∘ W=ᶠ[𝓝 0] purchaseG V P A i + presG S:=by
    filter_upwards [hV,liftable hs.leftF hS,Orbit.neighbo V.fly P (divides0 V.fly V.chain i) (ha.1 _) (camp_thaw ht).1 hQ] with y hv hm hs
    let M:=shiftH V.fly (divides0 V.fly V.chain i) P (A _) (Q y); have hE : (caravan P V.fly.wing A f (Q y)).det=M.det*(S y).det:=det_blocks _ (tied V.fly (divides0 V.fly V.chain i) 0 (Q y)) M (by unfold M shiftH caravan vaultF; abel) hs
    unfold rollG presG; simp only [Function.comp_apply]; rw [show input su f (W y) = Q y from hv.symm, show _= _ from hE,norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (show M.det≠0 from hs.ne_zero)) (norm_ne_zero_iff.mpr hm.ne_zero),neg_add]; rfl
  let O:=rollG P V.fly.wing A f
  have hn : Loves O:= rigL P V.fly.wing A ha f
  have hv:= tollsP _ hs.rightF H; have hm:=tollsP _ hs.leftF hS
  have hg:=repeated x x hh
  rw [Eyrie.summed x x hu hm.1,area_eval _ _ hF (show ContDiffAt ℝ ω O (W 0) from hW.symm ▸ hn.peak), hW,hx, hn.dew,add_zero] at hg
  apply hg.trans; congr 1; change Jacobi.mixed x x _ 0=Jacobi.mixed x x (presG Z) 0
  rw [hm.2,hv.2, hs.meet,hs.paint,hs.rep]
end YM.QCD.Raft
