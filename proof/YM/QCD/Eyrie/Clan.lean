import YM.QCD.Eyrie.Wing

/-! # using entry jets though matrix analytic after dimension fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Lat Kit Cost Finset Run Revolve Metric Push.Uniform Matrix
open YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {X Y R : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {n f:Side} {F : X → Matrix I J ℂ} {x : X}
lemma ink_touch (i : I)(j : J): ∃ L : Matrix I J ℂ →L[ℝ] ℂ, ∀ z, L z=z i j:= by
  let L : Matrix I J ℂ →ₗ[ℝ] ℂ := { toFun:=fun x=>x i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; exact ⟨L.toContinuousLinearMap,fun _=>rfl⟩
lemma matrix_g (h:∀ i j, ContDiffAt ℝ ω (fun x=>F x i j) x): ContDiffAt ℝ ω F x:=by
  let M (v:I→J→ℂ):Matrix I J ℂ:=v
  let L : (I→J→ℂ) →L[ℝ] Matrix I J ℂ:=LinearMap.toContinuousLinearMap {
    toFun:=M,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
  apply L.contDiff.contDiffAt.comp x (f:=fun y i j=>F y i j); exact contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr (h i)
lemma smear (h: ContDiffAt ℝ ω F x)(i : I)(j:J): ContDiffAt ℝ ω (fun x=> F x i j) x:=by
  obtain ⟨L,H⟩:=ink_touch i j; simp_rw [← H]; exact L.contDiff.contDiffAt.comp _ h
lemma detailed (h:ContDiffAt ℝ ω F x)(i : I)(j:J)(v:X):blade v F x i j=blade v (fun y=>F y i j) x:=by
  obtain ⟨L,H⟩:=ink_touch i j; simp_rw [← H]; exact (retell v L h).symm
lemma detail_sq (h:ContDiffAt ℝ ω F x)(i : I)(j:J)(v w:X):Jacobi.mixed v w F x i j=Jacobi.mixed v w (fun y=>F y i j) x:=by
  obtain ⟨L,H⟩:=ink_touch i j; simp_rw [← H]; exact (retold v w L h).symm
lemma inverse_ink {F : X→Matrix I I ℂ} (h:ContDiffAt ℝ ω F x) (he : IsUnit (F x).det): ContDiffAt ℝ ω (fun x=> (F x)⁻¹) x:=by
  have hz : (fun x=>(F x)⁻¹)=(fun x=> Ring.inverse (F x)):=by funext i; exact (Matrix.nonsing_inv_eq_ringInverse _)
  rw [hz]; have he : IsUnit (F x):= (F x).isUnit_iff_isUnit_det.mpr he
  obtain ⟨u,hu⟩:=he
  apply ContDiffAt.comp (g:=Ring.inverse) _ ?_ h; rw [← hu]; exact contDiffAt_ringInverse ..
lemma liftable {F:X→Matrix I I ℂ} (h:ContDiffAt ℝ ω F x)(hv : IsUnit (F x).det): ∀ᶠ y in 𝓝 x, IsUnit (F y).det:=by
  have he : ContinuousAt (fun y=>(F y).det) x:=by
    exact ((Continuous.matrix_det (A:=fun x:Matrix I I ℂ=>x) continuous_id).continuousAt).comp h.continuousAt
  exact (he.eventually_ne (isUnit_iff_ne_zero.mp hv)).mono fun _ hi=> isUnit_iff_ne_zero.mpr hi

-- agree precision and pack in any metric. general here.
variable {P Q:X→Y} {a C:ℝ}
structure Duet (P Q:X→Y) : Prop where
  leftF : ContDiffAt ℝ ω P 0
  rightF : ContDiffAt ℝ ω Q 0
  meet : P 0=Q 0
  paint (v:X): blade v P 0=blade v Q 0
  rep (v w:X): Jacobi.mixed v w P 0=Jacobi.mixed v w Q 0
lemma Duet.together (h: ContDiffAt ℝ ω P 0)(hg:P=ᶠ[𝓝 0] Q): Duet P Q:= ⟨h,h.congr_of_eventuallyEq hg.symm,hg.self_of_nhds,fun i=>blade_same i hg, fun i j=>repeated i j hg⟩
lemma Duet.flip (h:Duet P Q):Duet Q P:=⟨h.rightF,h.leftF,h.meet.symm,fun i=>(h.paint i).symm,fun i j=> (h.rep i j).symm⟩
lemma Duet.chain (h:Duet P Q){W:X→Y}(e:Duet Q W):Duet P W:=⟨h.leftF,e.rightF,h.meet.trans e.meet,fun i=>(h.paint i).trans (e.paint i),fun i j=>(h.rep i j).trans (e.rep i j)⟩
lemma summed (v w:X){u z:X→Y} (h:ContDiffAt ℝ ω u 0)(hz:ContDiffAt ℝ ω z 0): Jacobi.mixed v w (u+z) 0=Jacobi.mixed v w u 0+Jacobi.mixed v w z 0:= by
  rw [iter _ _ (f:=u+z) (h.add hz),iter _ _ h,iter _ _ hz,iteratedFDeriv_add_apply (h.of_le le_top) (hz.of_le le_top)]; rfl
lemma Duet.add (h:Duet P Q){V W:X→Y}(e: Duet V W): Duet (P+V) (Q+W):=by
  refine ⟨h.leftF.add e.leftF,h.rightF.add e.rightF,by simp only [Pi.add_apply,h.meet,e.meet],fun i=> ?_,fun i j=>?_⟩
  · change blade i (fun x=> P x+V x) _=blade i (fun x=>Q x+W x) _; rw [blade_plus _ h.leftF e.leftF,blade_plus _ h.rightF e.rightF,h.paint,e.paint]
  rw [summed _ _ h.leftF e.leftF,summed _ _ h.rightF e.rightF,h.rep,e.rep]
lemma Duet.redraw {Z:Type}{d : Z→X}{l:Z→Site f}{i:I→Site f}{j:J→Site f}{G : X→Matrix I J ℂ} (h:Duet F G)(he:glyph l d i j F a C):glyph l d i j G a C:=by
  intro x y; have hp:=he x y
  exact ⟨hp.fund,hp.fee,smear h.rightF ..,by rw [← h.meet]; exact hp.born,fun _=> by rw [← detailed h.rightF,h.paint _|>.symm,detailed h.leftF]; exact hp.walks _,fun _ _=> by rw [← detail_sq h.rightF,(h.rep ..).symm,detail_sq h.leftF]; exact hp.wandered _ _⟩

lemma jet_inv (F:X→Matrix I I ℂ) (h:ContDiffAt ℝ ω F 0)(he:IsUnit (F 0).det) :
    let A:= F 0; let K:=fun x=> ((A-F x)*A⁻¹)
    Duet (fun x=>A⁻¹ *(1+K x+K x*K x)) (fun x=>(F x)⁻¹) := by
  intro A K
  let B:= Matrix I I ℂ; let Q:=fun x=> A⁻¹*(1+K x+K x*K x)
  let U x := (F x)⁻¹; let R:=fun x=> U x*(K x*K x*K x)
  have hu : K 0=0:=by simp [K,A]
  have hg : ContDiffAt ℝ ω U 0:=inverse_ink h he
  have hz : ContDiffAt ℝ ω K 0:= (contDiffAt_const.sub h).mul contDiffAt_const
  have hv : ContDiffAt ℝ ω (Q) 0:= contDiffAt_const.mul ((contDiffAt_const.add hz).add (hz.mul hz));
  have hh : Duet (fun _=>0) R:=by
    let T x:= K x*K x
    have hT : ContDiffAt ℝ ω T 0:= hz.mul hz; let S x:= T x*K x; have hS : ContDiffAt ℝ ω S 0:=hT.mul hz
    have ht : T 0=0:=by simp [T,hu]
    have he : S 0=0:=by simp [S, ht]
    have h' (v:X): blade v T 0=0:=by unfold T; rw [made v hz hz,hu]; simp
    have hs (v:X): blade v S 0=0:=by unfold S; rw [made v hT hz,ht,hu]; simp
    have hr (v w:X): Jacobi.mixed v w S 0=0:=by unfold S; rw [rotate_area v w hT hz,ht,hu,h',h']; simp
    change Duet _ (fun x=> U x*S x); refine ⟨contDiffAt_const,hg.mul hS,(by rw [he,mul_zero]),fun i=>by rw [blade_const,made _ hg hS, hs,he]; simp,fun v w=>?_⟩
    rw [rotate_area _ _ hg hS,hs,hs,hr,he]; unfold Jacobi.mixed; rw [show blade w (fun x:X=> (0:Matrix I I ℂ))=(fun _=>0) from funext fun _=> blade_const ..,blade_const]; simp
  have hy : Q=(Q+(fun _=>0)):= by ext; simp
  have hm:= (Duet.together hv EventuallyEq.rfl).add hh
  rw [← hy] at hm; refine hm.chain (Duet.together hm.rightF ?_)
  filter_upwards [liftable h he] with x H; change Q x+U x * _ = _
  have hP : F x * A⁻¹=1-K x:=by unfold K; rw [sub_mul,Matrix.mul_nonsing_inv A he]; abel
  have hu : F x*Q x=1-K x*K x*K x:=by unfold Q; rw [← Matrix.mul_assoc,hP]; noncomm_ring
  apply Matrix.mul_right_injective_of_inv _ _ (Matrix.nonsing_inv_mul _ H)
  change F x*(Q x+U x*_) = F x * U x; rw [mul_add,hu,← Matrix.mul_assoc (F x) (U x),show F x*U x=1 from Matrix.mul_nonsing_inv _ H,one_mul]; abel
end YM.QCD.Eyrie
