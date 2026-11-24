import YM.Rill.Abode
/-! Two-sided slab calculus. Keep widths at native alignment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}(L:Pollens P Q) (a:Axis)
variable (p v w: Strip Q)(d:ℝ) {r:ℝ}
lemma unfoldE (x y: Strip Q)(s:ℝ): echo a s (x++y)= echo a s x ++ echo a s y:= traverse ..
variable (hQ:P.System) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {β e:ℝ}(hp:C.Path β e)(H:Q.Harmony P φ)
include hp hQ H hφ
lemma hinge (hM:manor p a d r)(hr:0<r)(hd:0 ≤ d)(hv:Sunny v a)(hw:Sunny w a): Strip.reach L a (tack p a d v) w = Strip.reach L a v (tack (partner L a d p) a d w):=by
    let P:= partner L a d p; unfold reach; rw[← Strip.migrates hQ hφ _ (d • basis a) hp H (aheadV L a _ _ (staying a hM hr hd hv) hw)]; apply congr_arg; change echo a d (oppositeS L a (p++ echo a d v) ++ w) = _; rw [nodes, reverseEcho,unfoldE,unfoldE,role,add_neg_cancel,restF]; change (oppositeS L a v ++ P) ++ (echo a d w)= _; rw [List.append_assoc]
omit hp hQ H hφ
-- width budgets.Strokes.
lemma echo_tape (s:ℝ)(x:Strip Q): (echo a s x).length=x.length:= List.length_map _
lemma partner_tape : (partner L a d p).length=p.length:=by simp [partner,echo,Strip.shifting,oppositeS]
-- pack M strict.To append using shared guard; any real r>0
lemma triple (hM:manor p a d r)(he:0<r){s:ℝ}(hu:manor w a s r)(hh:0≤ d)(hx:0 ≤ s): manor (p++echo a d w) a (d+s) r:=by
    constructor
    · have hv:gap (echo a d w) r:= hu.1.map _ (fun x y h=> by change r < dist (x.1+ d • basis a) (y.1+d • basis a); rw [dist_add_right]; exact h)
      refine List.pairwise_append.mpr ⟨hM.1,hv,fun x hg y hw=> ledger a _ _ r ?_⟩; rcases List.mem_map.mp hw with ⟨t,h,rfl⟩; change (t.1+d • basis a) a - _>_; rw [timing]; linarith [(hu.2 _ h).1,(hM.2 _ hg).2]
    intro i hi; rcases List.mem_append.mp hi with h|h
    · exact ⟨(hM.2 _ h).1,(hM.2 _ h).2.trans (sub_le_sub_right (le_add_of_nonneg_right hx) r)⟩
    obtain ⟨v,hV,rfl⟩:= List.mem_map.mp h; have h':=hu.2 _ hV; change ((v.1+d • basis a) a)∈ _; rw [timing]; constructor <;> linarith [h'.1,h'.2]
noncomputable abbrev whole (p:Strip Q) := partner L a d p ++ echo a d p
noncomputable abbrev climbY(p:Strip Q):= tack (whole L a d p) a (d+d)
lemma rise(y:Strip Q) : tack (partner L a d p) a d (tack p a d y) = climbY L a d p y:=by unfold tack climbY whole tack; rw [unfoldE,role,List.append_assoc] -- loops
include hp H hφ hQ
lemma evening (ht:manor p a d r)(hd:0≤d)(hr:0<r)(hv:Sunny v a)(hw:Sunny w a): Strip.reach L a (climbY L a d p v) w= Strip.reach L a v (climbY L a d p w):=by
    rw [←rise,← rise]; let g:=partner L a d p; have hp':manor g a d r:= partnerH L a ht; have hm:partner L a d g=p:=by
         unfold partner g; rw [partner, reverseEcho, twisted L p a H.h, role, add_neg_cancel, restF] -- binder
    have h1:= hinge L a _ (tack p a d v) w d hQ hφ hp H hp' hr hd (staying a ht hr hd hv) hw; rw [hm] at h1; change Strip.reach L a (tack g a d _) _=_; rw[h1]; exact hinge L a p v _ _ hQ hφ hp H ht hr hd hv (staying a ht hr hd hw)
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.hinge
#print axioms YM.Massive.Tarn.Quilt.triple
#print axioms YM.Massive.Tarn.Quilt.evening
