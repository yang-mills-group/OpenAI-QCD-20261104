import YM.Rill.Opal
/-! Filter at a physical pitch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}(L:Pollens P Q) (a:Axis)
variable (p:Strip Q)(d r:ℝ)(j:ℕ)(W:ℝ) (he:manor p a d r)(hr:0<r)(hd:0 ≤ d)
variable (G:∀ d,Cottage P d)(hS:Sway C.S) {β e:ℝ}(hp:C.Path β e) {φ:ℕ→ℕ} (H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop) (hP:P.System)
include hd hS G hp hφ hP H
lemma heat (v:Fin n → Strip Q) (hV:∀ i,Sunny (v i) a) (u:Fin n→ℂ):crestG L a n (echo a d ∘ v) u ≤ crestG L a n v u:=by
    let X : Strip Q → Strip Q:= tack [] a d; have hℓ: X=echo a d:= rfl
    have h0(s:ℝ):manor ([]:Strip Q) a s 1:=by simp [manor,gap]
    have hN:partner L a d []=[]:=rfl
    let Y:Strip Q→Strip Q:= (X∘ X); have hx(p:Strip Q)(h:Sunny p a):Sunny (X p) a:= staying a (h0 _) zero_lt_one hd h; have hf:∀ v w,Sunny v a→ Sunny w a→ Strip.reach L a (X v) w=Strip.reach L a v (X w):=fun v w hv hw=>by have h:= hinge L a [] v w d hP hφ hp H (h0 d) zero_lt_one hd hv hw; rw [hN] at h; exact h
    have hY:Y=tack [] a (d+d):=by funext z; change echo a d (echo a d z)=echo a (d+d) z; rw [role]
    rw [←hℓ,← one_mul (crestG L a n v u)]; refine mayor L a G hS hp H hφ hP X Y hx (fun x h=> hx _ (hx _ h)) (fun v w h k=> hf _ _ h (hx _ k)) (glueSym L a X X hx hx hf hf) 1 zero_lt_one ?_ v hV u
    intro v w hv hw; obtain ⟨A,hA,h⟩:=eternally L a G hS hp H hφ hv hw; refine ⟨_,hA,fun i=>?_⟩
    rw [one_pow,mul_one,hY,inherit]; have hi(m:ℕ):deckV a ([]:Strip Q) (d+d) m=[]:=by induction m with|zero=>rfl|succ m ih=>rw[deckV,ih]; rfl
    rw [hi]; exact h _ (by positivity)
include hr he
lemma packed (hD:∃ m: Cover,d•basis a=digit (C.S.spacing j) m)(hJ: List.length p*16<(C.S.step j).L.val)(hh:4*C.S.spacing j≤r)(hV:Admission P p j W)(hx:Admission P (partner L a d p) j W)(hw:1 ≤ W)(v: Fin n→ Strip Q)(hy:∀ i,Sunny (v i) a)(u:Fin n→ℂ):crestG L a n (tack p a d ∘ v) u ≤ ↑((W^p.length)^2)*crestG L a n v u:=by
    let X:= tack p a d; let Y:=climbY L a d p; let q:= whole L a d p; have hw':0 < W:=zero_lt_one.trans_le hw
    have e: manor q a (d+d) r:=triple a _ _ _ (partnerH L a he) hr he hd hd; have hm: Admission P q j W:=by intro z hz; rcases List.mem_append.mp hz with h|h; exact hx z h; obtain ⟨y,hY,rfl⟩:= List.mem_map.mp h; exact hV y hY
    have hz : List.length q=p.length*2:=by unfold q; rw [whole,List.length_append, partner_tape,echo_tape, mul_two] -- unfold q
    refine mayor L a G hS hp H hφ hP X Y (fun _=>staying a he hr hd) (fun _=> staying a e hr (add_nonneg hd hd)) (fun x v hv hy=>?_ ) (fun v w hv hw=> evening L a p v w d hP hφ hp H he hd hr hv hw) ((W^p.length)^2) (by positivity) ?_ v hy u
    · refine (hinge L a p x (X v) d hP hφ hp H he hr hd hv (staying a he hr hd hy)).trans (congr_arg (Strip.reach L a x) (rise L a p d v))
    intro v x hQ hx; have h':∃ m:Cover,(d+d) • basis a=digit (C.S.spacing j) m:=by obtain ⟨m,hh⟩:= hD; exact ⟨m+m,by rw [add_smul,hh,digit_plus]⟩
    obtain ⟨k,hk,h⟩:=powerS L a q (d+d) r j W e hr (add_nonneg hd hd) h' G hS hp H hφ (by rw [hz]; omega) hh hm hQ hx; refine ⟨k,hk,fun i=>?_⟩; rw [hz,pow_mul] at h; exact h i
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.heat
#print axioms YM.Massive.Tarn.Quilt.packed
