import YM.Rill.Stoke
import YM.Rill.Sure
/-! Strip padding, heat and alignment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}(L:Pollens P Q) (a:Axis)
variable (p v w: Strip Q) (r d:ℝ)
abbrev slab (p:Strip Q)(a:Axis)(d r:ℝ):Prop:= spaced r (locus p)∧ ∀ i∈p,i.1 a∈ Icc r (d-r)
abbrev manor (p:Strip Q)(a:Axis)(d r:ℝ):Prop:= gap p r ∧ ∀ i∈p, i.1 a∈ Icc r (d-r)
noncomputable def echo (a:Axis)(d:ℝ)(v:Strip Q):Strip Q:= Strip.shifting v (d • basis a)
noncomputable abbrev tack (p:Strip Q)(a:Axis)(d:ℝ)(v:Strip Q): Strip Q:= p ++ echo a d v
noncomputable abbrev partner (p:Strip Q):Strip Q:= echo a d (oppositeS L a p)
-- gaps real.E
lemma ledger (x y:E4)(r:ℝ)(h:y a-x a>r) : dist x y> r :=by apply lt_of_lt_of_le ?_ (PiLp.dist_apply_le x y a); rw [Real.dist_eq,abs_sub_comm]; exact h.trans_le (le_abs_self _)
variable {p v w r d}
lemma suburb {r t d:ℝ}(h:slab p a d t)(ht:r<t): manor p a d r:= ⟨List.pairwise_iff_get.2 (fun i j h'=>ht.trans_le ((h.1 i j (ne_of_lt h')).trans ((dist_pi_le_iff dist_nonneg).mpr fun b:Axis=> PiLp.dist_apply_le (locus p i) (locus p j) b))), fun i hi=> ⟨ht.le.trans (h.2 _ hi).1, (h.2 _ hi).2.trans (sub_le_sub_left ht.le d)⟩⟩
lemma entry (h:0<r)(hp:manor p a d r): Sunny p a:=by
    refine ⟨?_,fun x hx=>lt_of_lt_of_le h (hp.2 x hx).1⟩; rw [spots, List.Nodup]; apply hp.1.map; intro x y hL he; have hz: r<dist x.1 y.1:=hL; rw [he, dist_self] at hz; linarith
lemma timing (a:Axis) (b:ℝ)(x:E4): (x+b • basis a) a=x a + b:=by simp
lemma partnerH (hp:manor p a d r) : manor (partner L a d p) a d r:=by
     let f (x:TileV Q):TileV Q:=(Ortho.move (Signed.reflect a) x.1+d • basis a,L.adj a x.2); rw [show partner L a d p=p.reverse.map f from ?_]
     swap; · unfold partner oppositeS echo Strip.shifting; rw [List.map_map]; rfl
     have hv: gap p.reverse r:= by rw [gap,List.pairwise_reverse]; exact hp.1.imp fun x=>by rwa [dist_comm]
     refine ⟨hv.map _ (fun x y hx=>by change r<dist (_+_) (_+_); rw [dist_add_right]; exact ((Ortho.motion _).dist_map ..).symm ▸ hx),?_⟩
     intro x hx; obtain ⟨y,hy,rfl⟩:= List.mem_map.mp hx; obtain ⟨h,h'⟩:=hp.2 y (List.mem_reverse.mp hy); change _ ≤ ((Ortho.move (Signed.reflect a) y.1+d • basis a):E4) a ∧ ((Ortho.move (Signed.reflect a) y.1+d • basis a):E4) a ≤ d-r; rw [timing,Signed.mirrored]; simp only [↓reduceIte]; constructor<;>change ( _ :ℝ)≤_<;> linarith
lemma echo_sunny (s:ℝ)(hp:Sunny v a)(hs:0 ≤ s): Sunny (echo a s v) a:=by
     refine ⟨maintains _ _ hp.1,?_⟩; intro x h; obtain ⟨z,hz,h⟩:= List.mem_map.mp h; rw [←h,timing]; exact add_pos_of_pos_of_nonneg (hp.2 z hz) hs
lemma leaving (s:ℝ)(hp:Sunny v a)(i:TileV Q)(hx:i∈ echo a s v): s < i.1 a:=by
     obtain ⟨u,ht,rfl⟩:= List.mem_map.mp hx; change s < (u.1+s • basis a) a; rw [timing]; linarith [hp.2 u ht]
lemma staying {p v: Strip Q}(he:manor p a d r)(hr:0<r)(hd:0≤d) (hv:Sunny v a): Sunny (tack p a d v) a := by
    have hx:= entry a hr he; have hp:= echo_sunny a d hv hd; refine ⟨?_,?_⟩
    · rw [spots,tack,List.map_append,List.nodup_append]; refine ⟨(spots _).mp hx.1,(spots _).mp hp.1,?_⟩; intro x hx y hy hh; obtain ⟨v,h',rfl⟩:= List.mem_map.mp hx; obtain ⟨w,hV,rfl⟩:= List.mem_map.mp hy; apply not_lt_of_gt (lt_of_le_of_lt (he.2 _ h').2 (sub_lt_self d hr)); rw [hh]; exact leaving a d hv w hV -- not
    intro x hh; rcases List.mem_append.mp hh with H|H; exact hx.2 _ H; exact hp.2 _ H
lemma role (s t:ℝ)(u:Strip Q): echo a s (echo a t u)=echo a (s+t) u:=by unfold echo; rw[travel,add_comm s t, add_smul]
lemma restF(u:Strip Q): echo a 0 u=u:=by unfold echo; rw[zero_smul,rest]
lemma reverseEcho (s:ℝ)(u:Strip Q): oppositeS L a (echo a s u)= echo a (-s) (oppositeS L a u):=by unfold echo; rw [spinful,show Ortho.move (Signed.reflect a) (_•_)= _ from ?_]; ext i; by_cases h:i=a <;> simp [Signed.mirrored,h]
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.partnerH
#print axioms YM.Massive.Tarn.Quilt.suburb
#print axioms YM.Massive.Tarn.Quilt.staying
