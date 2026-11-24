import YM.QCD.Revolve.March

/-! # orient actual slots, including reversed backward faces and transports. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Function Lattice Wilson Lat Kit Cost Run Rudder Finset Set RG
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical
variable {a b : Step} {s : Signed}
lemma pricing (U:su.El): su.curvature U⁻¹= - su.curvature U:=by
  unfold Gauge.curvature; rw [inv_inv,← neg_sub,smul_neg,map_neg]
-- tag independent one/two-step slot rotation
structure Stays (a b:Step)(m:ℕ): Prop where
  path: ∃ (w:Walk)(q:PlaqAxes)(s:ℝ), |s|=1 ∧ w.length≤m ∧∀ (U : CoverConfig su)(x : Cover),
    su.curvature (travel U x (Lattice.oriented a b)) = s • su.adjoint (travel U x w) (su.curvature (faceValue U (stop x w,q)))
lemma toggle {m}(h:Stays a b m): Stays b a m:=by
  obtain ⟨w,q,s,hp,he,H⟩:= h.path; exact ⟨w,q,-s,by rw [abs_neg,hp], he,fun U x=>by rw [oriented_swap,pricing,H,neg_smul]⟩ -- structure Exists tricky
lemma positive_steps {i j:Axis}(h:i≠j): Stays (posDir i) (posDir j) 0:=by
  have hm (i j:Axis)(h:i<j) : Stays (posDir i) (posDir j) 0:= by
    refine ⟨[],⟨(i,j),h⟩,1,abs_one,le_rfl,fun U x=>?_⟩; rw [travel,Gauge.adjoint_one,one_smul]; rfl
  rcases lt_or_gt_of_ne h with h|h; · exact hm i j h
  exact toggle (hm j i h)
lemma reachLeft {i:Axis}{m}(h:Stays (posDir i) b m): Stays (negDir i) b (m+1):=by
  obtain ⟨w,q,c,hp,hu,H⟩:=h.path; refine ⟨negDir i::w,q,-c,by rw [abs_neg,hp],by simpa using hu,fun U x=>?_⟩
  let y:=x-step i; let a:=posDir i
  let A:=a.read U y; have he:y+a.vec=x:=by simp[y,a]
  have ht:= oriented_next a b y U; rw [he] at ht
  have hz:(negDir i).read U x=A⁻¹:= (he ▸ (Step.read_rev a U y)) -- risk
  rw [show Lattice.oriented (negDir i) b=Lattice.oriented a.rev b from rfl,oriented_swap b a.rev, pricing,ht,show a.read U y=A from rfl, show travel U x (negDir i::w)=_ from (show travel U x (negDir i::w)= A⁻¹ * travel U y w from by rw [travel,hz]; simp[y,a,sub_eq_add_neg])]
  have hk (B:su.El): su.curvature (A⁻¹* B *A)=su.adjoint A⁻¹ (su.curvature B):=by rw [← su.curvature_conjugate]; simp
  rw [hk, Gauge.adjoint_mul,H, map_smul,neg_smul]; simp [Lattice.stop,y,sub_eq_add_neg]
lemma attendance (a b:Step)(h:a.dir ≠ b.dir) : Stays a b 2:=by
  have hx {a b i j}(h:Stays a b i)(hk:i≤j):Stays a b j:=by obtain ⟨w,q,s,H,hv,ht⟩:=h.path; exact ⟨w,q,s,H,hv.trans hk,ht⟩
  rcases a with ⟨a,_|_⟩ <;> rcases b with ⟨b,_|_⟩
  · exact hx (positive_steps h) (by decide)
  · exact hx (toggle (reachLeft (positive_steps (Ne.symm h)))) (by decide)
  · exact hx (reachLeft (positive_steps h)) (by decide)
  exact reachLeft (toggle (reachLeft (positive_steps (Ne.symm h))))
lemma moved_stop {R:Type*} [AddCommGroup R] [One R] (s : Signed) (x : Four R)(w): s.act (stop x w)=stop (s.act x) (w.map (·.rotate s)):=by
  induction w generalizing x with
  | nil=>rfl
  | cons a w h=> rw [List.map_cons,stop,h,s.act_add,stop,← Step.vec_rotate]
structure Mint (s: Signed)(a w: RG.Slot)(r : ℝ): Prop where
  price : |r|=1
  offer : w.length≤a.length+2
  returnF (U:CoverConfig su) : a.eval (pull s 0 U)= r • w.eval U
lemma garment (s: Signed)(a: RG.Slot): ∃ w r, Mint s a w r:=by
  let f:=a.plaq; let u:=posDir f.val.1; let v:=posDir f.val.2; let q := a.walk.map (·.rotate s)
  obtain ⟨w,p,r,h1,h2,h3⟩:= (attendance (u.rotate s) (v.rotate s) (s.perm.injective.ne f.property.ne)).path
  refine ⟨⟨q++w,p⟩,r,h1,?_,fun V=>?_⟩
  · unfold Slot.length; dsimp only; unfold q; rw [List.length_append,List.length_map]; omega
  unfold Slot.eval faceValue; rw [travel_pull,travel_pull,show affine s (0:Cover) 0=0 by simp [affine],affine,add_zero,show List.map _ (Lattice.square a.plaq.val.1 a.plaq.val.2)=Lattice.oriented (u.rotate s) (v.rotate s) from ?_,h3]
  swap; · change (Lattice.oriented u v).map _= _; simp [Lattice.oriented,Step.rev_rotate]
  rw [map_smul, travel_append,Gauge.adjoint_mul, show s.act a.offset= stop (0:Cover) q from (moved_stop s 0 a.walk).trans (by simp [q]), Slot.offset, stop_append]; rfl
end YM.QCD.Revolve
