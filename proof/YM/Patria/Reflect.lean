import YM.Patria.Motion
import YM.QCD.Tide.Gleam
/-! Exact transport, adj. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {i j k d N n:ℕ}{c f r:Side}
open QCD.Revolve
open TorusPCAC.Geometry TorusPCAC.Finite TorusPCAC.Ward TorusPCAC.Geometry.AxisB Lining Lining.Ferry
open Next.Free
namespace Exposure
variable (M: StepData c f)(X: Density f 6)(Y: Density c 6)(a:Axis)(R:Regulator c 6)
abbrev eyeP (c:Side)(a:Axis) := Action.moved (F:=6) (n:=c) (Signed.mirror a) (gamma a)
local notation "s"=> Signed.mirror a
local notation "G"=> eyeP c a
local notation "V"=> Jobs c 6
local notation "T"=> copies 6 (hues (0:Site c) (Signed.mirror a) (prism s) (g5 * gamma a))
lemma motionG (u:Signed) (X Y: Spike) : Action.moved (n:=c) (F:=6) u (X*Y) = Action.moved u X*Jobs c 6 Y:=by rw [← stillB,roller,roller,roller, spar_spar]; congr 1; funext i; simp only [Signed.act_one,sheet_pace, one_smul, Matrix.smul_mul,Lat.wave_mul]
lemma orts  : eyeP c a*V g5=T:=by rw [rotor, star_mul, gamma_star,Lat.g5_star]; exact (motionG (Signed.mirror a) _ _).symm -- var shadow v!
lemma phase_sq : V g5*V g5=1:= pay _ _ g5_sq -- notation
lemma phase_star : star (V g5)=V g5:= (drum g5).trans (congr_arg _ g5_star)
lemma mirror_act (i:Site c): (Signed.mirror a).act ((s).act i)=i:=by rw [←Signed.act_mul, show (Signed.mirror a)*(s)=1 from mul_inv_cancel _,Signed.act_one]
lemma glowed (i:Site c): prism (Signed.mirror a) i*prism s ((s).act i)=1:=by
    let x:= (s).act (sheet i); have h: wrap c x = (s).act i:=by unfold x; rw [← wrap_signed,Ferry.sheet_unit]
    have hh: (s).act x=sheet i:=by unfold x; rw [← Signed.act_mul,show (s)*(s)=1 from mul_inv_cancel _,Signed.act_one]
    rw [← h]; exact (sheet_launch _ x s).trans (hh ▸ Ferry.sheet_pace _ _)
lemma eye_sq : eyeP c a*G=1:=by
    unfold eyeP; rw [roller,spar_spar]; refine Eq.trans (b:=spar id (fun (_:Site c)=>1)) ?_ spar_refl; congr 1; · exact funext (mirror_act a)
    funext i; change ((prism _ i) • _)*((prism _ _) • _)=_; rw [Matrix.smul_mul, Matrix.mul_smul,smul_smul, glowed,one_smul,wave_mul,gamma_sq,wave_one]
lemma eye_unit: eyeP c a∈ unitary _:=by
    have h:G=T * V g5:=by rw [← orts,mul_assoc,phase_sq,mul_one]
    rw [h]; exact Submonoid.mul_mem _ (copies_unitary _ _ (colour_wheel (smoke _) (Swing.mir _))) ⟨by rw [phase_star,phase_sq],by rw [phase_star,phase_sq]⟩
lemma eye_star: star (eyeP c a)=G:=by calc star G=star G* (G* G):=by rw [eye_sq,mul_one];
                                                       _=_:=by rw [←mul_assoc,(eye_unit a).1,one_mul]
lemma eye_moved (u:Signed) (X:Spike) : Action.moved (n:=c) (F:=6) u (-X)= -Action.moved u X:=by
    ext i j; simp only [Action.moved, Matrix.of_apply, Revolve.wave_neg,Matrix.neg_apply]; split <;> simp
lemma eye_value (U: Grid c) : Action.adj a Y U= tilt G (Y (pull s 0 U)):=by
    unfold Action.adj; rw [eye_moved,eye_moved,show Action.moved s (gamma a) (n:=c) (F:=6) =G from rfl]; let A:= dagger (Y (pull s 0 U)); change changeVars (Matrix.fromBlocks 0 (-_) (-G) 0) A= adapter (-G) (-G)ᵀ (embed Sum.swap A)
    have h: Action.moved s (gamma a)ᵀ (n:=c) (F:=6)=(G)ᵀ:=by
       rw [← eye_star a (c:=c), ←mstar_sq]; change _= Mstar (Action.moved s (gamma a)); rw [dir_sail,mstar_sq,gamma_star]
    rw [h]; refine AlgHom.congr_fun (φ₂:=(adapter (-G) (-G)ᵀ).comp (embed Sum.swap)) (ext_atoms fun i=>?_) A
    cases i <;> simp [adapter, change_atom,Fintype.sum_sum_type]
section beam
lemma reel (U: Grid f): TorusPCAC.meanSpin (N:=6) M (pull s 0 U)= G*TorusPCAC.meanSpin M U*star (eyeP f a) :=by
    have he:M.ratio.embed 0=0:= map_zero M.ratio.root; have ht:= stencil_pull (N:=6) (Swing.mir a) M (b:=0) (l:=prism s) (by rw [he]; exact smoke s) U
    rw [he,show prism s ∘ M.ratio.embed=prism s from funext fun _=> step_prism ..,← orts,← orts] at ht
    rw [ht,star_mul,phase_star]; let X:= TorusPCAC.meanSpin (N:=6) M U; let Vb:=Jobs f 6 g5
    let H:=star (eyeP f a); change (G*(V g5)*X)*(Vb*H) = _
    calc _=(G*((V g5)*X))*(Vb*H):= congr_arg (· * (Vb*H)) (Matrix.mul_assoc ..)
         _=(G*(X*Vb))*(Vb*H):=congr_arg (fun x=> (G*x)*(Vb*H)) (free_slots M U g5).symm
         _= G* (X * H):=by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vb Vb, phase_sq,Matrix.one_mul]
         _=_:=(Matrix.mul_assoc ..).symm
lemma eye_high(U:Grid f): tilt G (TorusPCAC.high M X (pull s 0 U))= TorusPCAC.high M (Action.adj a X) U:=by
    let A:= eyeP f a; let C:= Kit.whole A G; have hC:star C=C:=by unfold C; rw [Kit.whole_star,eye_star,eye_star]
    have hΘ:C*C=1:=by unfold C; rw [Kit.whole,Matrix.fromBlocks_multiply]; simp only [show A*A=1 from eye_sq _,eye_sq,Matrix.zero_mul,Matrix.mul_zero,add_zero]; ext (i|i) (j|j) <;> simp [Matrix.one_apply]
    let B:=TorusPCAC.meanSpin (N:=6) M U; let Y:= Kit.joinD 1 B 0
    have hh : star Y=Y:=by unfold Y Kit.joinD; rw [Matrix.star_eq_conjTranspose]; simp [Matrix.fromBlocks_conjTranspose]
    have hu: tilt C (gauss (Kit.joinD 1 (G*B*star A) 0))= gauss Y:=by
         have hv:= Kit.rotate_join A G (eye_unit a) (eye_unit a) 0 B 1; rw [mul_zero,zero_mul] at hv; rw [hv]; apply Tide.tiltingX; change C*(star (C*Y*star C)*C)=Y; rw [star_mul,star_mul,hh,star_star C,hC]; simp [mul_assoc,hΘ]; rw [←mul_assoc,hΘ,one_mul]
    unfold TorusPCAC.high; rw [eye_value,reel,Kit.sheath]; simp only [Complex.ofReal_one, inv_one,one_pow,one_smul]; let W:= X (pull s 0 U)
    rw [Tide.studied A G (eye_star _) (eye_sq _) (eye_star _) (eye_sq _),tilt_mul,hu,Tide.studio,← (gauss_plus Y).central _]; simp only [Kit.sheath, Complex.ofReal_one, inv_one,one_pow,one_smul,Y,B]; rfl
-- same regulator
lemma eye_shiftB (he:R.t=0)(W:Grid c): star (R.D (pull s 0 W))=G*R.D W*G:=by
    let Hr:=V g5; let D:=R.D W; have hv:R.D (pull s 0 W)=T*D*star T:=by
        -- Eq
        unfold D Regulator.D Lat.copies; rw [block_star,←Matrix.blockDiagonal_mul,←Matrix.blockDiagonal_mul,he]; exact congr_arg Matrix.blockDiagonal (funext fun i=> bare_cov (Swing.mir a) (smoke _) W _)
    have hp : star D= Hr* D *Hr:=by unfold Hr D Regulator.D Jobs copies; rw [block_star,←Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]; exact congr_arg Matrix.blockDiagonal (funext fun _=> gamma5 ..)
    rw [hv,← orts,star_mul,star_star,star_mul,star_mul,eye_star,phase_star,hp]; change G*Hr*(Hr* D*Hr*(Hr*G))=_; simp only [mul_assoc]; rw [← mul_assoc Hr Hr, show Hr*Hr=1 from phase_sq,one_mul, ← mul_assoc Hr Hr, show Hr*Hr=1 from phase_sq,one_mul]
lemma eye_pivot (he:R.t=0) : Action.adj a R.density=R.density:=by funext U; rw [eye_value]; change tilt G ((_ : ℂ) • gauss _)= _; rw [map_smulₛₗ,bare_pull]; simp only [Complex.conj_ofReal,Regulator.density_apply]; apply congr_arg (fun i:Fields c 6=> (bare R.β U:ℂ) • i); apply Tide.tiltingX; rw [eye_shiftB _ _ he]; rw [mul_assoc (G*_),eye_sq, mul_one, ←mul_assoc,eye_sq,one_mul] -- loops simp
lemma eye_temp (x: Lat.Fields c 6)(w:ℝ): tilt G (temp (w:ℂ) x)=temp (w:ℂ) (tilt G x):=by
    unfold temp; rw [tilts,tilts,turns,adapt_together,adapt_together]; simp [Twist]
abbrev realTilt {c:Side} (M:Matrix (Modes c 6) (Modes c 6) ℂ) : Lat.Fields c 6 →L[ℝ] Lat.Fields c 6:= LinearMap.toContinuousLinearMap ({ toFun:=⇑(tilt M), map_add':=map_add (tilt M), map_smul':= fun t x=> by change tilt M ((t:ℂ) • x)=_; rw [map_smulₛₗ]; simp} : Lat.Fields c 6 →ₗ[ℝ] Lat.Fields c 6) -- spin
lemma eye_shift (h:M.patch.Branches M.kernel su) (w v:ℝ)(hp:Continuous X) : Action.adj a (TorusPCAC.block M w v X)= TorusPCAC.block M w v (Action.adj a X):=by
    funext U; rw [eye_value,TorusPCAC.block]; let f' := TorusPCAC.high M X; change tilt G (temp _ (M.push w f' (pull s 0 U)))= _; have he : Continuous f':= high_cont M X hp
    rw [eye_temp,push_pull M h w s _ _ f' he, show M.ratio.embed 0=0 from map_zero M.ratio.root]; let L := realTilt G; let g(W:Grid f):=f' (pull s 0 W); have hg: Continuous g:= he.comp (continuous_pull ..)
    rw [show tilt G (M.push w g U) = ∫ x:Grid f,L (M.density w x U • g x) ∂prior su f from (L.integral_comp_comm (StepData.push_slice (M.isKernel h w) U _ (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)))).symm]; simp_rw [map_smul L, show ∀ x:Grid f,L (g x)=TorusPCAC.high M (Action.adj a X) x from eye_high M X a]; rfl
end beam
end Exposure
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Exposure.eye_unit

#print axioms YM.Massive.Patria.Exposure.eye_shift
#print axioms YM.Massive.Patria.Exposure.eye_pivot
