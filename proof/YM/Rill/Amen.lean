import YM.Rill.Seats
/-! Real placement of uniform stencil tests. Collect exterior-independent constants under powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}(L:Pollens P Q) (a:Axis)
abbrev Admission (P:Calibration C) (w:Strip Q)(j:ℕ)(v:ℝ):=∀ i∈w,Privilege P Q j i.2 v
variable (p:Strip Q)(d r:ℝ)(j:ℕ)(W:ℝ) (he:manor p a d r)(hr:0<r)(hd:0 ≤ d)
noncomputable def deckV (a:Axis)(p:Strip Q)(d:ℝ)(m:ℕ):Strip Q:=match m with |0=>[]|n+1=>p++ echo a d (deckV a p d n)
variable (hC:∃ m: Cover,d • basis a=digit (C.S.spacing j) m)
include he hr hd
lemma decks (n:ℕ):manor (deckV a p d n) a (n*d) r:=by
    induction n with|zero=> simp only [deckV,manor,List.not_mem_nil,false_implies,implies_true,and_true]; simp [gap] |succ n ih=> have hv:=triple a p (deckV a p d n) d he hr ih hd (show (0:ℝ) ≤ n*d by positivity); rw [deckV,Nat.cast_add, Nat.cast_one,add_mul,one_mul, add_comm]; exact hv -- args
omit he hr hd
lemma inherit (n:ℕ): (tack p a d)^[n]= tack (deckV a p d n) a (n*d):=by
    funext v; induction n with
    | zero=> simp [tack,deckV,restF]
    | succ n ih=> rw[Function.iterate_succ_apply',ih,deckV]; unfold tack; rw [unfoldE,role,List.append_assoc,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm d]
lemma railing (n:ℕ): List.length (deckV a p d n)=n*p.length:=by induction n with|zero=>simp [deckV]| succ n ih=> rw[deckV,List.length_append, echo_tape,ih, add_comm p.length,Nat.succ_mul]
include hC
lemma heels (n:ℕ)(H:Admission P p j W):∀ i∈ deckV a p d n,(∃ z:Fin p.length, Scan C j (locus p z) i.1) ∧ Privilege P Q j i.2 W:=by
    obtain ⟨q,hq⟩:= hC; induction n with| zero=>simp[deckV]|succ n ih=>
     intro i hi; rw[deckV,List.mem_append] at hi; rcases hi with h|h
     · refine ⟨?_,H i h⟩; obtain ⟨z,rfl⟩:=List.mem_iff_get.mp h; exact ⟨z,0,by rw[digit_zero,add_zero]; rfl⟩
     obtain ⟨i,h',rfl⟩:=List.mem_map.mp h; obtain ⟨⟨z,w,ht⟩,hp⟩:=ih i h'; refine ⟨⟨z,w+q,?_⟩,hp⟩; change i.1+d • basis a=_; rw[ht,hq,digit_plus,add_assoc]
variable (G:∀ d,Cottage P d)(hS:Sway C.S) {β e:ℝ}(hp:C.Path β e) {φ:ℕ→ℕ} (H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)
variable {v w:Strip Q}
include hC hr he hd G hS hp H hφ
set_option maxHeartbeats 450000 in
lemma powerS (hT: p.length * 8 < (C.S.step j).L.val)(hh:4*C.S.spacing j≤r)(hY:Admission P p j W)(hv:Sunny v a)(hw:Sunny w a):∃ B:ℝ,0 ≤ B∧∀ m:ℕ, ‖reach L a v ((tack p a d)^[m] w)‖≤ B * (W^p.length)^m :=by
     let V:= oppositeS L a v; obtain ⟨ℓ,hj,Z,hZ,hL⟩:= Privilege.post L a G hS hp H hφ (j+1) ((V.length+w.length)*6+1) hv hw; let b:= Z^(V.length+w.length); have hz:0 ≤ Z:= zero_le_one.trans hZ
     refine ⟨b,by unfold b; positivity,fun m=>?_⟩; let s:ℝ:=m*d; have hs:0 ≤ s:=by unfold s; positivity
     let X:=deckV a p d m; let Y:= echo a s w; let l:=V++ X++ Y; have he: manor X a s r:=decks a p d r he hr hd m; change ‖Strip.tone _‖≤_; rw [inherit]; unfold tack; rw [← List.append_assoc]
     have hk:∀ x∈V++Y,∀ y∈X, 4*C.S.spacing j < dist x.1 y.1:=by
          intro x hx y hy; rcases List.mem_append.mp hx with h|h; · have hx:=darkens L a v hv _ h; apply ledger a; linarith [(he.2 y hy).1]
          have hx:= leaving a s hw _ h; rw [dist_comm]; apply ledger a; linarith [(he.2 y hy).2]
     have h:= hL s hs; refine (plaza hp H hφ V X Y j ℓ W Z (locus p).ofLp hj (?_ : Fintype.card (Fin p.length)*8 < _) ?_ (he.1.imp fun x=>hh.trans_lt x) h.2.2 hk h.2.1 (heels a p d j W hC m hY)).trans ?_
     · simpa using hT
     · unfold Y; rw [echo_tape]; exact h.1
     change Z^(V.length+Y.length)* W^X.length≤_; rw [show Y.length=w.length from echo_tape .., show X.length=p.length*m from (railing a p d m).trans (Nat.mul_comm ..), pow_mul]
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.powerS
