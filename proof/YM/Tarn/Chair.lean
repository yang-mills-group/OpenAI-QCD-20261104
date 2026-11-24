import YM.Tarn.Wheels
/-! Universal pre-space on the authentic scale family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Zodiac Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag.Vale
open scoped Topology ContDiff BigOperators Classical
open Function Sash
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
variable {Z:SpaceZ}(H:Ability P φ Z)(h:Cresc Z){M:∀ d:ℕ,Axis→Label d→ₗ[ℂ] Label (d+2)} (he:Gains M Z)
variable (s: Sash G φ) (hz:DriftF G φ)
structure Choir where
    W :Type
    [ab:NormedAddCommGroup W]
    [space:NormedSpace ℂ W]
    focus (u:Averaging)(d:ℕ): Label d→ₗ[ℂ] W
    total (n:ℕ): Points n→ MultilinearMap ℂ (fun _:Fin n=> W) ℂ
    arc (a:Axis): W →ₗ[ℂ] W
attribute [instance] Choir.ab Choir.space
namespace Choir
variable (Q: Choir)
noncomputable def level(d:ℕ):= LinearMap.range (Q.focus none d)
structure Domestic : Prop where
    tops (u d): LinearMap.range (Q.focus u d)= Q.level d
    slope: Monotone Q.level
    faith(d):Module.finrank ℂ (Q.level d)= Module.finrank ℂ (UV.Free.Symbol d)
    absorbs(w:Q.W):∃ d,w∈Q.level d
    derivatives(n:ℕ)(x:Points n)(hx:x∈conf n)(t:Fin n→Q.W)(p:Fin n)(a:Axis):YM.Analysis.D (Points.direction p a) (fun x=> Q.total n x t) x= Q.total n x (Function.update t p (Q.arc a (t p)))
    graded(a:Axis)(d:ℕ)(x:Q.W)(hx:x∈Q.level d):Q.arc a x∈Q.level (d+2)
    smooth(n:ℕ)(t:Fin n→ Q.W):ContDiffOn ℝ ∞ (fun x=> Q.total n x t) (conf n)
    thick(n:ℕ)(t:Fin n→ Q.W)(j:ℕ):∃ m:ℕ,∃ A:ℝ,0 ≤ A∧∀ r:ℝ,0 < r → r ≤ 1 →∀ x:Points n,spaced r x→ ‖iteratedFDeriv ℝ j (fun x=>Q.total n x t) x‖≤ A*r⁻¹^m
    listens (v:Q.W)(hx:v≠0):∃ x:E4,(∀ a:Axis,0 < x a)∧∃ w:Q.W, Q.total 2 (points ![0,x]) ![w,v] ≠ 0
structure Harmony (P:Calibration C)(φ:ℕ→ℕ):Prop where
    h: Domestic Q
    trueLimit(n:ℕ)(x:Points n)(hx:x∈conf n)(d:Fin n→ℕ)(u:Fin n→ Averaging)(v:(i:Fin n)→Label (d i)): Exposes C φ (fun k p=> eyeW P d u (φ k) p v) x (Q.total n x (fun i=> Q.focus (u i) _ (v i)))
variable {Q}
include hp hr H hφ hz s G
set_option maxHeartbeats 490000 in
lemma uplift : ∃ Q:Choir, Q.Harmony P φ :=by
    obtain ⟨M,he⟩:= derives hp hr hφ s H hz; have h:= builds hp hr hφ H s hz; obtain ⟨F,hF⟩:= partials h he
    let Θ:=foliage Z; let B (u:Averaging)(d:ℕ): Label d→ₗ[ℂ] Θ:= (plume Z d).comp (pointsR s d u)
    have hx(d:ℕ): B none d= plume Z d:=LinearMap.ext fun p=>Subtype.ext (funext fun i=> (s.grasp hp hr hφ H d i.t i.p p i.x i.hx).symm)
    letI := YM.Tarn.nerve ↥Θ; letI := YM.Tarn.starry ↥Θ
    let Q:Choir:=⟨Θ,B,sphere Z h,F⟩; have hv(d:ℕ): Q.level d = LinearMap.range (plume Z d):=by change LinearMap.range (B none d)= _; rw [hx d]
    refine ⟨Q,⟨⟨fun u d=> ?_, fun i j hij=>?_, fun d=>?_,fun u=>?_,fun n x hx t p a=>?_, fun a d x hx'=>?_,fun n t=> gloss h he t, fun n t j=> sheen hp hr hφ H h he (G:=G) t j,fun v hx=>cant hp hr hφ H h s v hx⟩,fun n x hx d u v=>?_⟩⟩
    · rw [hv,← rafters hp hr hφ H s]; change LinearMap.range (B u d)=_; apply le_antisymm; · rintro _ ⟨p,rfl⟩; exact ⟨s.A u d p,rfl⟩
      rintro _ ⟨p,rfl⟩; obtain ⟨v,hx⟩:=s.rich hp hr hφ d u p; rw [←hx]; exact ⟨v,rfl⟩
    · rw [hv,hv]; exact h.growth hij
    · -- Q.W subtype.Instances, use inject map rank
      change Module.finrank ℂ ↥(LinearMap.range (B none d))= _; rw [hx,← rafters hp hr hφ H s]; exact ((LinearEquiv.ofInjective _ (caulk hp hφ H s d)).finrank_eq.symm).trans (by simp [CellF,Stokes,Module.finrank_pi])
    · obtain ⟨d,p,hp⟩:= h.sealed u; exact ⟨d,show u ∈ LinearMap.range (B none d) from hx d |>.symm ▸ (show u∈LinearMap.range (plume Z d) from ⟨p,hp⟩)⟩
    · exact bearings h he t F hF x hx p a
    · obtain ⟨p,hp⟩:= (show x∈LinearMap.range (plume Z d) from hv d ▸ hx'); refine hv _|>.symm ▸ (show Q.arc a x∈LinearMap.range (plume Z (d+2)) from ⟨M d a p,?_⟩); rw [←hp]; exact (hF d a p).symm
    let q(i:Fin n):TagF:= ⟨d i,s.pointsR _ (u i) (v i)⟩; have he': Q.total n x (fun i=> Q.focus (u i) _ (v i))=handle Z q x:= cosmos Z hx h q (fun i=> B (u i) _ (v i)) (fun _=>rfl); rw [he']; exact guide hp hr hφ s H d u v x hx
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.uplift
