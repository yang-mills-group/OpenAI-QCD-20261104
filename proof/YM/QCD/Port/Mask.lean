import YM.QCD.Port.Hearth
/-! # Exact unitary and Bool transforms in place. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Sway
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q w Ω π κ:ℝ}{b B i:ℕ}{j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{X:St f}{W:ℕ→Atom su 2}
local notation "Mx"=> Modes c F
local notation "S"=> sliceL L H
variable (P : Swathe L H X W J u v η p q b)
variable {s : Strut c} {Z:Spike} {r: Site f →ℂ} {T:Ratio c f}
-- symmetry exact, W.P includes anchors and read robe. integer
abbrev hoops (T:Ratio c f)(p:Strut c): Equiv.Perm (XMark f):= Equiv.optionCongr (raiseS T p)
lemma oak {I J:Type*}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]{x:I→Site f}{y:J→Site f}{A:Therm I T x}{B:Therm J T y}{X:Land f I J}(h:Held T A B X)(hv: Warrant (raise T s) r Z)(p:Site f)(z:XMark f)(i j b)(U:Grid f):
   chipK p b X i j z (settled (sky (raise T s) U))=lightP (raise T s) Z r (x i)*chipK (act (raise T s) p) b X (A.shiftP s i) (B.shiftP s j) (hoops T s z) (settled U)*star (lightP (raise T s) Z r (y j)):=by
    cases z
    next=>
       rw [show hoops T s none=none from rfl]; simp only [chipK,spoon,Finset.sum_apply, hike T s b p,Matrix.mul_sum,Matrix.sum_mul]; exact sum_congr rfl fun i' _=> radS h hv U i j i'
    next z=> rw [show hoops T s (some z)=some (raiseS T s z) from rfl]; simp only [chipK]; simp only [whittled T s b p z]; split; exact radS h hv U i j z; simp
lemma sheer (a:XMark f)(x:Site c)(b:ℕ) (U:Grid f)(h: Warrant (raise S s) r Z):
    batch S P.bath x a b (settled (sky (raise S s) U))= aura (chair S (dot S) s Z r) (batch S P.bath (act s x) (hoops S s a) b (settled U)):=by
   apply whist; intro i j; unfold aura chair; rw [stack,cell_ride_right,cell_ride_left,stack]
   change sale _ _ _ (_)=_ *sale _ (act s i) (act s j) _*star _; rw [oak P.glow h,peaks]; simp only [sale,EmbeddingLike.apply_eq_iff_eq,Matrix.mul_smul,Matrix.smul_mul]
lemma ray_touch (x y:Bundle)(h:y∈unitary _): (y*x*star y).trace=x.trace:=by rw [Matrix.trace_mul_comm,← mul_assoc,h.1,one_mul]
lemma scalarH (h:Warrant (raise S s) r Z) (x:Site f)(z:XMark f)(b U): chalkF P.walk x z b (settled (sky (raise S s) U))=chalkF P.walk (act (raise S s) x) (hoops S s z) b (settled U) := by
  have he :sky (raise S s) 1=1:=by funext i; unfold sky pull Step.read; simp
  have hh:=oak P.puff h x z x x b (1:Grid f); rw [he] at hh
  unfold chalkF; rw [oak P.puff h x z x x b U, hh, ray_touch _ _ (license h _), ray_touch _ _ (license h _)]; rfl
-- rotation law ornament
abbrev tagJump (T: Ratio c f)(w:Strut c): Equiv.Perm (Varn f c):= Equiv.sumCongr (Equiv.prodCongr (act (raise T w)) (hoops T w)) (Equiv.prodCongr (act w) (hoops T w))
open OrbitG
lemma rayTrade (R:Matrix Mx Mx ℂ)(hR:R∈unitary _)(A B:Sheet c)(h: Lat.copies F A=R * Lat.copies F B*star R): (trade R).passL (paleF F A)=paleF F B:=by
  apply Subtype.ext; change disguise R (form (Lat.copies F A))=form (Lat.copies F B); rw [h,disguise,form_map, Matrix.transpose_transpose]; simp only [Matrix.mul_assoc, hR.1,one_mul,mul_one]; rw [← Matrix.mul_assoc (star R),hR.1,one_mul]
lemma ray_const (R:Matrix Mx Mx ℂ)(x:ℂ): (trade R).passL (sparkF c F x)=sparkF c F x:=by
  apply Subtype.ext; change disguise R (light _ (sparkF c F x))=light _ (sparkF c F x); rw [service,map_smul,map_one]
lemma royalties (F:ℕ)(x:Varn f c)(B:ℕ)(U:Grid f)(h:Warrant (raise S s) r Z): (trade (Lat.copies F (chair S (dot S) s Z r))).passL (sliceF P F B x (sky (raise S s) U))=sliceF P F B (tagJump S s x) U:=by
  rcases x with ⟨i,j⟩|⟨i,j⟩
  · simp only [sliceF,Sum.elim_inl, ray_const]; rw [scalarH P h]; rfl
  apply rayTrade _ (copies_unitary F _ (trail (mist S s h))) _ _; rw [sheer P j i B U h,aura, show ∀ Q M:Sheet c,-(Q*M*star Q)=Q*(-M)*star Q from fun Q M=>by rw [Matrix.mul_neg,Matrix.neg_mul]]; exact podium ..
lemma pump (x:Varn f c)(w: Strut c)(b:ℕ):(payT T b x).image (act (raise T w))=payT T b (tagJump T w x):= by
   let F:=act (raise T w); let p:=orbitM T x
   have ht :orbitM T (tagJump T w x)=F p:=by
      cases x; · rfl
      next=> exact (peaks w T _).symm
   have hw: waxV (tagJump T w x)=hoops T w (waxV x):=by cases x <;> rfl
   unfold payT; rw [ht,hw]; generalize waxV x=z; cases z
   · change (trunkFt p b).image F=trunkFt (F p) b
     unfold trunkFt; rw [← halo_map F (Push.Local.turn_sep _ _),image_singleton]
   next z=> change (insert p z).image F=insert (F p) (raiseS T w z); rw [image_insert,show raiseS T w z=z.image F from Finset.map_eq_image ..]
lemma triumph (F b:ℕ)(x:Varn f c)(U:Grid f)(g: Frame f): (trade (rotates F (g ∘ (S).embed))).passL (sliceF P F b x (gauge g U))=sliceF P F b x U:=by
  rcases x with ⟨i,j⟩|⟨i,j⟩
  · simp only [sliceF,Sum.elim_inl,ray_const, chalkF]; rw [(cups P.att i i i b j).2.2.2.2.2 U g,ray_touch _ _ (touch_u _)] -- touch_u implicit he?
    exact ⟨su.mat_star_mul _,su.mat_mul_star _⟩
  apply rayTrade _ (rotates_law ..); let X:= siteRot (g ∘ (S).embed)
  have he : batch S P.bath i j b (settled (gauge g U))=X * batch S P.bath i j b (settled U)* star X:=by
    apply whist; intro p q; unfold X siteRot; rw [stack,cell_ride_right, cell_ride_left,stack,(cups P.arcP ((S).embed i) p q b j).2.2.2.2.2 U g]; simp only [sale,Matrix.mul_smul,Matrix.smul_mul]; rfl
  rw [he, show ∀ Q M:Sheet c,-(Q*M*star Q)=Q*(-M)*star Q from fun Q M=>by rw [Matrix.mul_neg,Matrix.neg_mul]]; exact podium ..
end YM.QCD.Port
