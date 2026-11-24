import YM.Fir.Rings
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
/-! Mesh-to-classical all-slot genuine derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Analysis YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric TagF
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology ContDiff BigOperators Classical
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
variable (s:Sash G φ)
variable {Z:SpaceZ}(H:Ability P φ Z)(hz:DriftF G φ)
variable (M: ∀ d:ℕ,Axis→Label d→ₗ[ℂ] Label (d+2))
noncomputable def turnsH (t: Fin n→TagF)(p:FrameI n):Fin n→TagF:= update t p.1 ⟨(t p.1).1+2,M _ p.2 (t p.1).2⟩
noncomputable def litH (Z:SpaceZ)(x:Points n)(t:Fin n→TagF): Points n→L[ℝ]ℂ:=(wing (fun b=> handle Z (turnsH M t b) x)).comp (crossing n).toContinuousLinearMap
structure Gains (Z:SpaceZ): Prop where
    fields (n:ℕ) (x:Points n)(hx:x∈conf n)(t: Fin n→ TagF): HasFDerivAt (handle Z t) (litH M Z x t) x
open Sash
variable {M}
include hp hφ
set_option maxHeartbeats 420000 in
private lemma sounding (t:Fin n→TagF)(x:Points n)(hx:x∈conf n)(hV:∀ y∈conf n, Exposes C φ (fun j=>aperture C (packTag P t) (φ j)) y (handle Z t y))(hh:∀ b:FrameI n,Exposes C φ (fun i=>tube C (packTag P t) b.1 (fun k=> lDer C k b.2 (packTag P t b.1 k)) (φ i)) x (handle Z (turnsH M t b) x)): HasFDerivAt (handle Z t) (litH M Z x t) x:=by
    let U:= packTag P t; let a(k):=C.S.spacing (C.N (φ k)); let y:=crossing n x; let f(k:ℕ):= aperture C U (φ k) ∘ (jade n).symm; let F:= handle Z t ∘ (crossing n).symm; let T (b:FrameI n):=handle Z (turnsH M t b) x
    have h:HasFDerivAt F (wing T) y:=by
         refine appeared (fun _=>space0 _ _) ((tendsto_nhds_of_tendsto_nhdsWithin hp.physical).comp hφ) (f:=f) ?_ ?_
         · have hq: (crossing n).symm y=x:= (by unfold y; rw [ContinuousLinearEquiv.symm_apply_apply]); have h':∀ᶠ p in 𝓝 y,(crossing n).symm p∈conf n:= ((crossing n).symm.continuous.tendsto y).eventually ((conf_open n).mem_nhds (hq.symm ▸ hx))
           filter_upwards [h'] with i hi; have hb:= (nNote ..).mp (hV _ hi); rw [ContinuousLinearEquiv.apply_symm_apply] at hb; exact hb
         intro b; let D:= (hh b).comp (rouses x); apply D.congr; rintro ⟨k,p⟩
         let i:= φ k; let u:= (jade n).symm p; change tube C U b.1 (fun k=> lDer C k b.2 (U b.1 k)) i u = _; rw [raises]; have hy: jade n (advanced b.1 b.2 u)=advanceF b p:= (by rw [brightF,show jade n u=p from Equiv.apply_symm_apply ..]); have ht:(jade n).symm (advanceF b p)= advanced b.1 b.2 u:=by rw [← hy,Equiv.symm_apply_apply]
         change _= (a k)⁻¹ • (aperture C U i ((jade n).symm (advanceF b p))-aperture C U i u); rw [ht]
    have hm:= h.comp x (crossing n).hasFDerivAt; have he: handle Z t = F ∘ crossing n:=by unfold F; ext1 x; simp
    rw [he]; exact hm
include H hr hz s
lemma derives :∃ M: ∀ d:ℕ,Axis→ Label d→ₗ[ℂ]Label (d+2), Gains M Z:=by
    choose M h using fun i b=> steer hp hr hφ s H hz i b; refine ⟨M,⟨fun n x hx t=>?_⟩⟩; refine sounding (P:=P) hp hφ _ x hx ?_ ?_
    · intro y hy; exact (H.excels n (fun i=>(t i).1) y hy fun i=> (t i).2)
    exact fun b=> h _ b.2 n t x hx b.1 (t b.1).2
omit H hp hr hz s hφ
namespace Gains
variable (h:Gains M Z)
include h
omit h in
local instance sunny (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance
lemma openD (x:Points n)(hx:x∈conf n)(t:Fin n→TagF)(p:Fin n)(a:Axis): D (Points.direction p a) (handle Z t) x= handle Z (turnsH M t (p,a)) x:=by
    unfold D; rw [(h.fields n x hx t).fderiv]; unfold litH; rw [ContinuousLinearMap.comp_apply,show ((crossing n).toContinuousLinearMap (Points.direction p a))= _ from pivotF p a,thornF] -- order check h.fields hx etc
lemma partsH (d:ℕ)(a:Axis)(v:Label d)(x:Points n)(hx:x∈conf n)(t: Fin n→TagF)(p:Fin n): D (Points.direction p a) (fun x=> puts Z x t p d v) x= puts Z x t p _ (M d a v):=by
     let T':Fin n→TagF:= update t p ⟨d,v⟩; change D _ (handle Z T') _ = handle Z _ _; rw [h.openD x hx T' p a]; apply feel_eq; intro i; change update T' p ⟨(T' p).1+2,M _ a (T' p).2⟩ i= update t p ⟨d+2,M d a v⟩ i; rw [show T' p=⟨d,v⟩ from update_self ..]; unfold T'; rw [update_idem]
set_option maxHeartbeats 420000 in
lemma smooth (t:Fin n→TagF): ContDiffOn ℝ ∞ (handle Z t) (conf n):=by
    apply contDiffOn_infty.mpr; intro i; induction i generalizing t with
    | zero=> simp only [Nat.cast_zero,contDiffOn_zero]; exact fun x hx=> (show HasFDerivAt (handle Z t) (litH M Z x t) x from h.fields n x hx t).differentiableAt.continuousAt.continuousWithinAt
    | succ i ih=>
         rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (conf_open n).uniqueDiffOn]; refine ⟨by simp, (fun y=> litH M Z y t), ?_,fun y hy=>(h.fields n y hy t).hasFDerivWithinAt⟩
         apply contDiffOn_clm_apply.mpr; intro y; let F(b:FrameI n)(x:Points n):= handle Z (turnsH M t b) x; have he:(fun x=> litH M Z x t y)=fun x:Points n=> ∑ b,(crossing n y b) • F b x:= funext (fun _=> pin ..); rw [he]; exact ContDiffOn.sum (fun b _=> (ih _).const_smul _) -- order
end Gains
end YM.Massive.Fir
#print axioms YM.Massive.Fir.derives
#print axioms YM.Massive.Fir.Gains.smooth
