import YM.QCD.Fog.Body

/-! # Local α matching. the density mismatch exploited only after summing the oriented channels. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration QCD.Smoke Work.F03
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {E: Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a x₀:ℝ}{M: Before su u v E.J K N}
variable (V:Back E K j k p u v) (J:Plan j){U:On}
-- effective real det log
def purchaseG (T:On)(i:ℕ)(x:Cnr (V.chain.n i)):= -Real.log ‖(shiftH V.fly (divides0 V.fly V.chain i) J (T _) (encamp (V.port.forest i) (V.port.u i) x).1).det‖
variable (hp:Arbor J E.L k 1 w q g R δ Y B)(hU:Vital U)(hr:0<r)(he:0≤D)(h:Plume V J M U r D w)
include hp hU
lemma currency (i:ℕ): purchaseG V J U i=ᶠ[𝓝 0] fun x=> summaryP V J U w i x+(Fintype.card (Row (localG V i)):ℝ)*Real.log w:=by
  let X z:=(encamp (V.port.forest i) (V.port.u i) z).1
  let P x:=shiftH V.fly (divides0 V.fly V.chain i) J (U _) (X x)
  have hz : X 0=1:=by unfold X; rw [encamp_zero (V.port.critical i)]; rfl
  have hh:= (camp_thaw (V.port.critical i)).1
  have he := (hU.1 (localG V i))
  have ha: ContinuousAt P 0:= (ContinuousAt.add ((canopy ..).continuousAt.comp hh.cont) ((mir_ink_sync hh hz he.2.2.2.2).continuousAt))
  have hu : ContinuousAt (fun x=> (P x).det.re) 0:= Complex.continuous_re.continuousAt.comp ((Continuous.matrix_det (A:=fun i:Sheet (localG V i)=> i) continuous_id).continuousAt.comp ha)
  have hx : 0 < (P 0).det.re:=by unfold P shiftH; rw [hz,he.2.2.2.1,add_zero]; exact ticket_pos ..
  filter_upwards [hu.eventually (lt_mem_nhds hx),comfort V J i (V.port.critical i) hU hp] with x hx hh
  change 0 < (P x).det.re at hx
  have hJ:Chiral (chirality (localG V i)) (P x):=by
    unfold P shiftH Chiral; have hg:=ticketStar J V.fly (divides0 V.fly V.chain i) 0 (X x)
    have hp':= (funds0 _).mp (he.2.1.lane (X x)).symm; unfold Chiral at hg hp'
    rw [star_add,hg,hp',mul_add,add_mul]
  let F:= P x; let Z (y:Site (localG V i)):= (Run.cell (lap (notch w F)) y y).trace.re
  let Q:= Fintype.card (Row (localG V i))
  change -Real.log ‖F.det‖= _
  rw [show ‖F.det‖=F.det.re from ?_, stamped F hJ hx hp.pos hh,neg_sub]
  · let g:= (sliceL V.fly (divides0 V.fly V.chain i)); have hh : summaryP V J U w i x= -(∑ y,Z y):=by
      rw [← Equiv.sum_comp g.splitSites.symm Z,Fintype.sum_prod_type, ← Finset.sum_neg_distrib]; rfl
    rw [hh]; change _ - ∑ y,Z y= _; ring
  conv_lhs=> rw [← determinant_real chi_sq hJ,Complex.norm_real,Real.norm_of_nonneg hx.le]
include hr he h
lemma spark_price (i): ContDiffAt ℝ ω (purchaseG V J U i) 0 ∧ (∀ x, blade x (purchaseG V J U i) 0=0) ∧ ∀ x y, Jacobi.mixed x y (purchaseG V J U i) 0=Jacobi.mixed x y (summaryP V J U w i) 0:=by
  have he':= currency V J hp hU i; let S:=summaryP V J U w i; have hS:=summedP V J hU hr he h i
  refine ⟨(hS.add contDiffAt_const).congr_of_eventuallyEq he',fun i'=> ?_,fun z y=>?_⟩
  · rw [blade_same _ he', blade_plus _ hS contDiffAt_const, blade_const,add_zero]; exact emptyP V J hU hr he h i _
  rw [repeated _ _ he']; let a:ℝ := ↑(Fintype.card (Row (localG V i))) * Real.log w; change Jacobi.mixed z y (summaryP V J U w i+(fun _=>a)) 0=_; rw [Eyrie.summed z y hS contDiffAt_const]; rw [show Jacobi.mixed z y (fun _=>a) 0=0 from ?_,add_zero]
  unfold Jacobi.mixed; rw [show blade y (fun (_:Cnr (V.chain.n i))=>a)=(fun _=>0) from funext fun _=>blade_const y a]; exact blade_const z 0
variable (Z:Bed)(hZ : Z.metric.strip a A)(hζ:Z.metric.read 0=1)(hQ:∀ i,Bid.Sworn Z (V.chain.n i) su)

def Capes (V:Back E K j k p u v)(A:ℕ→ Atom su 2)(α:ℝ)(Z: Bed)(r c :ℝ) (T:On)(J:Plan j): Prop:= 0 < r ∧∀ i, ContDiffAt ℝ ω (purchaseG V J T i) 0 ∧(∀ x,blade x (purchaseG V J T i) 0=0) ∧ ∀ x, let F:= arm su _ 1 x
    ‖Jacobi.mixed x x (purchaseG V J T i) 0-(α*Bid.gaugeFiscal Z F F +2*Patch.average fun s:Signed=>total (Iteration.plain∘A) (flux (Bid.pulled F s)))‖ ≤ (Fintype.card (Site (V.chain.n i)):ℝ)*(c*Real.exp (-r*(localG V i).val))*‖x‖^2

include hZ hζ hQ
def Pcost (E:Patch)(D r a:ℝ):= Smoke.auction a (creditP E r D)
lemma raisons (hA:0< a)(hh: 4*a ≤ r/4) (hd:0<x₀)(hx:x₀<a): ∃ (β:ℝ)(I:Type)(_ : Countable I)(P:I→PairG su), Palisade P x₀ (momentPrice 2 (a-x₀)*(Real.exp (12*a)*(cycleTax A a*Pcost E D r a))) ∧ |β| ≤ 2*Pcost E D r a ∧ Capes V (installG P) β Z (r/2) (leafPrice E D r) U J:= by
  obtain ⟨W,m,H⟩:= attainH V.chain _ (fun i=> incensed V J hU hr he h i)
  let X:= strata W
  have hv := soldSym (fun i=>incensed V J hU hr he h i) H
  have hC := credit_nn E r he
  have hy : Charged (strata W) a (Pcost E D r a):=sold H hh hA hC
  refine ⟨twice X,_,inferInstance,inertia Z X, lic hv hZ hA hy hζ hd.le hx,?_,by positivity, fun i=>?_⟩
  · rw [twice,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact deposit_bound X hy hA
  have hp' := spark_price V J hp hU hr he h i
  refine ⟨hp'.1,hp'.2.1,fun x=>?_⟩
  let F:=arm su (V.chain.n i) 1 x
  have hv' := stratus V J hp hU hr he h H i x hh hA
  have hv'' :∀ s:Signed, total (Iteration.plain ∘ padded (strata W)) (flux (Bid.pulled F s))=total (Iteration.plain ∘ X) (flux (Bid.pulled F s)) := fun i=> total_padded hy hA.le _
  change ‖_-(twice X*Bid.gaugeFiscal Z F F+2* _)‖≤ _
  rw [hp'.2.2,voteG _ _ (fun s=> figurines hv hZ hA hy hζ hd.le hx (hQ i) F s)]
  let d:=Patch.average (fun i:Signed=> total (Iteration.plain∘ strata W) (flux (Bid.pulled F i)))
  rw [show (_:ℝ)+2*(d-_) = 2*d from ?_]; swap
  · unfold X; unfold d; ring
  simp_rw [show ∀ s:Signed,total _ (flux (Bid.pulled (arm su (V.chain.n i) 1 x) s)) = _ from hv''] at hv'; exact hv'
end YM.QCD.Fog
