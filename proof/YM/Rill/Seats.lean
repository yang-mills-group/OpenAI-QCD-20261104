import YM.Rill.Mood
/-! Exterior-cap energy. Uniform spacing under long translation. Needn't reduce B multiplicities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}(L:Pollens P Q) (a:Axis)
variable {p v w: Strip Q} (d:ℝ) {r:ℝ}
namespace Privilege
variable (G:∀ d,Cottage P d)(hr:Sway C.S) {β e:ℝ}(hp:C.Path β e) {φ:ℕ→ℕ} (H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)
lemma growth {j:ℕ} {x:Q.W}{u v:ℝ}(h: Privilege P Q j x u)(hx:u ≤ v):Privilege P Q j x v:=by obtain ⟨k,p,hF,hK⟩:=h; exact ⟨k,p,hF,hK.mono fun i hi=>GreenP.mono hi hx⟩
include G hr H
lemma singleton (v:Q.W):∀ᶠ j in atTop,∃ t:ℝ,0 ≤ t ∧ Privilege P Q j v t:=by
    obtain ⟨d,p,hp⟩:=H.h.tidal v none; let F:= (G d).rise; filter_upwards [F.nest] with j hj; exact ⟨_,mul_nonneg (norm_nonneg p) (F.power j),d,p,hp,hj.mono (fun i hi=> hi _)⟩
lemma atlas (l:Strip Q): ∀ᶠ j in atTop,∃ t:ℝ,1 ≤ t∧∀ v∈l,Privilege P Q j v.2 t:=by
    induction l with
    | nil=> exact Eventually.of_forall fun j=> ⟨1,le_rfl,by simp⟩
    | cons a l ih=> filter_upwards [ih,singleton G hr H a.2] with j hj h; obtain ⟨t,ht,hh⟩:=hj; obtain ⟨s,hs,h⟩:=h; refine ⟨max s t,ht.trans (le_max_right ..),fun v hv=>?_⟩; rcases List.mem_cons.mp hv with e|e; rw [e]; exact h.growth (le_max_left ..); exact (hh v e).growth (le_max_right ..)
omit G hr H
-- exterior.P heights
lemma stroll (hv:Sunny v a)(hw:Sunny w a):∀ᶠ s in 𝓝[>] (0:ℝ),∀ d:ℝ,0 ≤ d → gap (oppositeS L a v ++ echo a d w) s:=by
    let V:= oppositeS L a v; have hu(v:Strip Q)(hv:Strip.distinct v): ∀ᶠ s in 𝓝[>] (0:ℝ), gap v s:=by
         let I:= {ij:Fin v.length×Fin v.length // ij.1 < ij.2}; have he:∀ᶠ s in 𝓝[>] (0:ℝ),∀ i:I,s < dist (locus v i.val.1) (locus v i.val.2):= eventually_all.mpr fun i=> eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (dist_pos.mpr ((show Injective (locus v).ofLp from hv).ne (ne_of_lt i.property))))
         exact he.mono fun i hi=> List.pairwise_iff_get.2 fun j k h=> hi ⟨(j,k),h⟩ -- binder
    have hj:∀ᶠ s in 𝓝[>] (0:ℝ),∀ i: Fin V.length,s < -((V.get i).1 a):=eventually_all.mpr fun i=> eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (neg_pos.mpr (darkens L a v hv _ (List.get_mem ..))))
    filter_upwards [hu _ (dimV L a v hv.1),hu w hw.1,hj] with s hs hx hh d hd; exact List.pairwise_append.mpr ⟨hs,hx.map _ (fun x y ht=>by change s < dist (_+_) (_+_); rwa [dist_add_right]),fun x h y he=>by
          obtain ⟨j,hj⟩:= List.mem_iff_get.mp h; refine ledger a _ _ _ ?_; have hb:=leaving a d hw y he; rw [←hj]; have hh:s< -((V.get j).1 a):=hh j; change s < _- (V.get j).1 a; linarith only [hh,hb,hd]⟩
include G hp H hφ hr
lemma post (j I:ℕ)(hv:Sunny v a)(hw:Sunny w a): ∃ ℓ≥j, ∃ Z:ℝ, 1 ≤ Z∧∀ s:ℝ, 0 ≤ s → ((I ≤ (C.S.step ℓ).L.val) ∧ (∀ z∈ oppositeS L a v ++ echo a s w, Privilege P Q ℓ z.2 Z)∧ gap (oppositeS L a v ++ echo a s w) (4*C.S.spacing ℓ)):=by
     let B:= oppositeS L a v; obtain ⟨r,hr',hQ⟩:= ((stroll L a hv hw).and self_mem_nhdsWithin).exists; change 0 < r at hQ; obtain ⟨N,hN⟩:= eventually_atTop.mp ((atlas G hr H (B++w)).and (hr.high.eventually_ge_atTop I)); obtain ⟨ℓ,hℓ,hv⟩:= shyness hp (r/4) (by positivity) (max j N); obtain ⟨⟨Z,hZ,hp⟩,hl⟩:=hN ℓ ((le_max_right ..).trans hℓ); refine ⟨ℓ,(le_max_left ..).trans hℓ,Z,hZ,fun s hs=>⟨hl,fun z hz=>?_ , (hr' s hs).imp fun x=> lt_trans (show 4*C.S.spacing ℓ<r by linarith only [hv]) x⟩⟩; rcases List.mem_append.mp hz with e|e; · exact hp _ (List.mem_append.mpr (Or.inl e))
     obtain ⟨t,ht,rfl⟩:=List.mem_map.mp e; exact hp t (List.mem_append.mpr (Or.inr ht))
end Privilege
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.Privilege.post
