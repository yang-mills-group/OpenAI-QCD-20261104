import YM.ValeK.Mirth
import YM.Alum.Rally
import YM.Alum.Daisy

/-! # Purchase relative probe gauges. Box strictly off every axis projections. before-L constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Vale
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
variable {d:ℕ}(sym:UV.RawSym)(H:Laurel d)
local notation "A"=> Stokes d
local notation "w" => fun _ : Fin 2 =>d
local notation "B"=> basis timeAxis
local notation "X"=> sym.adj d timeAxis
-- arrange coordinates physical.Mark exact ε seq
lemma Φcts (i j:A): ContinuousAt (fun x=> ΦGram sym H x i j) B:=by
     let g(x:E4):= points ![(0:E4),x]; let p:= (opposite sym timeAxis (H.F i)).mark; let q:=(H.F j).mark; let L:=UV.Free.moment (w)
     have hp:g B ∈ conf 2:=by have h:= DawnS.distinct 1 zero_lt_one; rw [show g B= _ from ?_]; exact h; unfold g DawnS.dotsG DawnS.prelude; rw[one_smul]
     have hg:Continuous g:=by unfold g points; fun_prop
     have ht:= UV.Free.Sip.smoothC hp w (fun i=> (labels d).subtype (![p,q] i)); exact ht.continuousAt.comp hg.continuousAt
open Metric
-- Oxygen witness gauge.Any f.. Segment strict gap rectangle all e′≤e,v'≥v . Error to wick true values asked ≤δ. Gives ε/4 margin calibrate projections via held.View.Operator.
structure Landing (sym:UV.RawSym) (H:Laurel d) where
    a:E4
    (l ε J v e:ℝ)
    light:0 < ε
    breadth : 0 < l
    fee:0 ≤ J
    far : 0 < e
    north : 0 < v
    warmth {f:A→A→ℂ}:nearG sym H ε f→∀ x:A→ℂ, ‖x‖ ≤ J * ‖Γ f x‖
    pose (x:E4)(hx:x∈closedBall a l) : ![0,x]∈ Ibis.flats (Fin 2) (3*e) (v/4) ∧(∀ i:Axis, 2*e≤ x i)∧(∀ i j : A,‖ΦGram sym H x i j- ΦGram sym H B i j‖ < ε/2)
lemma visited : Nonempty (Landing sym H):=by
   obtain ⟨ε,J,hp,hJ,hW⟩:= herd sym H
   have hN:∀ᶠ x:E4 in 𝓝 B,∀ i j:A,‖ΦGram sym H x i j- ΦGram sym H B i j‖ < ε/2:= eventually_all.mpr (fun i=>eventually_all.mpr fun j=> Metric.tendsto_nhds.mp (Φcts sym H i j) _ (half_pos hp)|>.mono fun x hx=> by rwa [dist_eq_norm] at hx)
   obtain ⟨b,hb,hF⟩:=Metric.mem_nhds_iff.1 hN -- hN eventually.As mem
   let p:E4:=∑ i:Axis,basis i
   let f(t:ℝ):= B+t • p; have ht : Tendsto f (𝓝[Set.Ioi 0] 0) (𝓝 B):= (by rw [show 𝓝 B=𝓝 (f 0) by simp[f]]; exact (show Continuous f by unfold f; fun_prop).continuousAt.continuousWithinAt)
   obtain ⟨t,hp1,hy⟩:= ((ht.eventually (Metric.ball_mem_nhds B hb)).and self_mem_nhdsWithin).exists
   have h1:0<t:=hy; let x:= f t; have hx(i:Axis):0< x i:=by unfold x f p; by_cases hi:i=timeAxis <;> simp [hi, h1] <;> linarith
   have hn:0<‖x‖:=norm_pos_iff.mpr fun e=>by specialize hx 0; rw[e] at hx; exact lt_irrefl _ hx
   let v:=16*‖x‖; have hv:0<v:=by unfold v; positivity
   let F:= 𝓝[Set.Ioi (0:ℝ)] 0; have hE:∀ i:Axis, ∀ᶠ y in F,2*y<x i:=fun i=> Eventually.filter_mono nhdsWithin_le_nhds ((show ContinuousAt (fun y:ℝ=> 2*y) 0 from by fun_prop).eventually_lt continuousAt_const (by simp [hx i]))
   obtain ⟨e,h2,h3⟩:= ((eventually_all.mpr hE).and (((show Tendsto (fun y:ℝ=>3*y) F (𝓝 0) from (by simpa only [ContinuousWithinAt,mul_zero] using (show ContinuousWithinAt (fun t:ℝ=>3*t) (Set.Ioi 0) 0 from (show Continuous (fun t:ℝ=>3*t) from by fun_prop).continuousAt.continuousWithinAt))).eventually_lt_const hn).and self_mem_nhdsWithin)).exists
   have hz:∀ᶠ z:E4 in 𝓝 x,(3*e ≤ ‖z‖ ∧ ‖z‖ ≤ v/8 ∧ ∀ i:Axis,2*e ≤ z i)∧ ∀ i j,‖ΦGram sym H z i j- ΦGram sym H B i j‖ < ε/2:=by
         have hY:∀ᶠ z:E4 in 𝓝 x,∀ i: Axis,2*e < z i:= eventually_all.mpr fun i=> continuousAt_const.eventually_lt (show ContinuousAt (fun z:E4=> z i) x from by fun_prop) (h2 i)
         filter_upwards [(show ∀ᶠ z:E4 in 𝓝 x,3*e < ‖z‖ from continuousAt_const.eventually_lt continuous_norm.continuousAt (show 3*e < _ from h3.1)),continuous_norm.continuousAt.eventually_lt_const (show ‖x‖ < v/8 from (by unfold v; linarith)),hY,isOpen_ball.mem_nhds (show x∈ball B b from hp1)] with z h hq hP hm
         exact ⟨⟨h.le,hq.le,fun i=> (hP i).le⟩,hF hm⟩
   obtain ⟨l,hl,hL⟩:=Metric.mem_nhds_iff.mp hz
   refine ⟨x,l/2,ε,J,v,e,hp,half_pos hl,hJ,h3.2,hv,hW _,fun y h=>?_⟩
   obtain ⟨⟨h1,h₂,h₃⟩,hH⟩:= hL ((Metric.closedBall_subset_ball (half_lt_self hl)) h)
   refine ⟨(Ibis.outward ..).2 ⟨?_,?_⟩,h₃,hH⟩
   · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; fin_cases i
     · change ‖(0:E4)‖ ≤ _; rw [norm_zero]; positivity
     change ‖y‖ ≤ _; linarith only [h₂]
   intro i j he; fin_cases i <;> fin_cases j <;> first | contradiction|simpa using h1
end YM.Intag.Vale
#print axioms YM.Intag.Vale.visited
