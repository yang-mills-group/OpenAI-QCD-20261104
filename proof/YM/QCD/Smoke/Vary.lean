import YM.QCD.Smoke.Scene

/-! # onsite diagonal shell probes -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Finset Lat Cost Run Eyrie Metric Lattice Wilson Push.Uniform Kit Pine Sparks Orbit Birth RG Flume
open YM.Further.PhysicalPeriodLimitF933 Jacobi Quarry Revolve
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.L2Operator
variable {n c f:Side}{j k:ℕ}
lemma lap_orbit (M:Sheet n)(D:Sheet n)(h:D∈unitary _) (w:ℝ): lap (notch w (aura D M))=aura D (lap (notch w M)):=by
  obtain ⟨L,hL⟩:= auraCL D; obtain ⟨R,hR⟩:= auraCL (star D)
  have hI : Function.LeftInverse R L:=fun x=>by simp_rw [hR,hL]; exact compatible D x h
  set X:=notch w M
  have he: notch w (aura D M)=aura D X:=by unfold notch X; rw [notch,aura_sub,aura_one h,aura_scale]
  have hh(k:ℕ):logchip (aura D X) k = L (logchip X k):=by
    have hz (i:ℕ): aura D (X^i)=(aura D X)^i:= by induction i with
                                                 | zero=>simp [aura_one h]
                                                 | succ i ih=>rw [pow_succ,pow_succ,aura_prod h,ih]
    rw [hL,logchip,logchip,aura_neg,aura_scale,hz]
  rw [he,lap,lap,← hL (∑' k, logchip X k)]; simp_rw [hh]
  exact (Function.LeftInverse.map_tsum (g:=L) _ L.continuous R.continuous hI).symm -- inspect
lemma cell_h (V:Equiv.Perm (Site n))(M:Site n→Bundle) (F:Sheet n)(x y): Run.cell (aura (rides V M) F) x y=M x*Run.cell F (V x) (V y)*star (M y):=by
  let X:=rides V M; have he (z:Site n): Run.cell (X*F) x z=M x*Run.cell F (V x) z:=by
    rw [cell_mul,sum_eq_single (V x), show Run.cell X x (V x)=M x from ?_]; exact (by ext i j; simp [Run.cell,X,rides])
    · intro i _ hi; rw [show Run.cell X x i=0 from ?_,zero_mul]; ext a r; simp [Run.cell,X,rides,Ne.symm hi]
    simp
  unfold aura; change Run.cell (X*F*star X) _ _=_; rw [cell_mul,sum_eq_single (V y),he]
  · congr 1; rw [show star X=Xᴴ from rfl,cell_flip]; exact congr_arg star (by ext a r; simp [cell,X,rides])
  · intro b _ hb; rw [show star X=Xᴴ from rfl,cell_flip,show Run.cell X y b=0 from by ext i j; simp [cell,X,rides,Ne.symm hb], star_zero,mul_zero]
  simp
lemma glow_h (V:Equiv.Perm (Site n))(M:Site n→Bundle)(F:Sheet n)(h:rides V M∈unitary _)(x): (Run.cell (aura (rides V M) F) x x).trace=(Run.cell F (V x) (V x)).trace:=by
  have hh : (M x)*star (M x)=1:=by
    have ht:= cell_h V M 1 x x; rw [aura_one h,cell_one,cell_one,if_pos rfl,if_pos rfl,mul_one] at ht; exact ht.symm
  rw [cell_h,Matrix.trace_mul_comm,← Matrix.mul_assoc, show star _ * M x=1 from mul_eq_one_comm.mpr hh,one_mul]

def heartP (ρ:Ratio c f)(A: Sheet f) (x: Site c):ℝ:= -(∑ j:Site ρ.count,(Run.cell A (ρ.assemble (x,j)) (ρ.assemble (x,j))).trace.re) -- effective action -log
lemma shineP (ρ:Ratio c f)(u:Frame f)(A:Sheet f)(x:Site c): heartP ρ (aura (siteRot u) A) x=heartP ρ A x:=by
  unfold heartP; simp_rw [siteRot, glow_h _ _ _ (siteRot_u u),Equiv.refl_apply]
lemma assemble_affine (ρ:Ratio c f)(x y:Site c)(z:Site ρ.count)(s:Signed)(h:Odd ρ.count.val): affine s (ρ.embed y) (ρ.assemble (x,z))=ρ.assemble (affine s y x,s.act z):=by
  unfold affine; rw [← Ratio.assemble_signed ρ h]; unfold Ratio.assemble; dsimp only; rw [show ρ.embed (s.act x+y)=ρ.embed (s.act x)+ρ.embed y  from ρ.root.map_add (s.act x) y]; abel
lemma beacon (ρ:Ratio c f)(V:Signed)(d:Site c)(u:Site f→ℂ)(q:Spike)(h:hues (ρ.embed d) V u q∈unitary _)(hr:Odd ρ.count.val)(F:Sheet f)(x:Site c):
    heartP ρ (aura (hues (ρ.embed d) V u q) F) x=heartP ρ F (affine V d x):=by
  unfold heartP; congr 1
  rw [← Equiv.sum_comp (V.actEquiv (R:=Per ρ.count)).toEquiv (fun j => (Run.cell F (ρ.assemble (affine V d x,j)) (ρ.assemble (affine V d x,j))).trace.re)]; apply sum_congr rfl; intro y _
  rw [hues,glow_h _ _ F h]; change (Run.cell _ (affine V (ρ.embed d) (ρ.assemble (x,y))) (affine V (ρ.embed d) (ρ.assemble (x,y)))).trace.re= _; rw [assemble_affine ρ x d y V hr]; rfl
end YM.QCD.Smoke
