import YM.TorusPCAC.Geometry.Pull
import YM.Massive.Lining.Daymark
import YM.Massive.Target.Tower
/-! TorusPCAC transport uses exactly the same step on full fields; keep KernelChoices. Bridge to actual Cup schedule. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {i j k d N n:ℕ}{c f r:Side}
open Next.Free
section
variable (S:Flight j k)(K:KernelChoices) (h:f.val=c.val*S.L.val) (s w:ℝ)(F:Density f N)
local notation "P"=> coarse S K h
lemma soften_alt : soften S h F=TorusPCAC.high (coarse S K h) F:= rfl
lemma rescale_alt (w:ℝ): rescale (c:=c) (F:=N) w=TorusPCAC.rescaleSpin w:=by
    unfold rescale TorusPCAC.rescaleSpin adapter; apply congr_arg; ext (i|i) (j|j) <;> by_cases he:i=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply, he]
lemma step_brute : transfer S K h s w F=TorusPCAC.block (coarse S K h) s w F:=by unfold transfer; rw [rescale_alt, soften_alt S K]; rfl
lemma torusDensity (R:Regulator c N) : ⇑R.density=(⟨R.t,R.β,R.m⟩:TorusPCAC.Torus c N).weight:=rfl
end
open QCD.Revolve
open TorusPCAC.Geometry
variable (s:Signed)(b:Cover)(p:EuPin)
-- actual AP sign, not restricted to short struts. Child sign for mirror etc.
abbrev prism (s:Signed) (x:Site c):= ap c (s.act (Cylinder.sheet x))
lemma shimmers (t:Step)(x:Cover): ap c (x+t.vec) = ap c x*glint (0:Site c) (wrap c x) t:=by
    rcases t with ⟨a,_|_⟩
    · exact TorusPCAC.Geometry.thermal_step x a
    let y:=x-step a; let t:=posDir a; have he: y+t.vec=x:=sub_add_cancel x _; have hv: wrap c y+t.vec=wrap c x:= by rw [← wrap_vec c t,← map_add,he]
    change ap c (x+-(step a)) = ap c x * glint (0:Site c) (wrap c x) t.rev ; rw [←sub_eq_add_neg]; have h:ap c x= ap c y*glint (0:Site c) (wrap c y) t:=he ▸ TorusPCAC.Geometry.thermal_step y a; rw [h,← hv,glint_rev,mul_assoc,glint_sq,mul_one]
lemma smoke : Glare s (0:Site c) 0 0 (prism s):=by
    refine ⟨fun i=>TorusPCAC.Geometry.signs _, fun i x=>?_⟩
    let q:= sheet x; let t := (posDir i).rotate s; have h0 : wrap c q=x:= Lining.Ferry.sheet_unit ..
    have h : ap c (s.act (q+step i))=prism s x*glint (0:Site c) (affine s 0 x) t:=by rw [show s.act (q+step i)= s.act q + t.vec by rw [Signed.act_add]; exact congr_arg (fun v' : Cover=> s.act q+v') (Step.vec_rotate (posDir i) s).symm, shimmers,← wrap_signed,h0,affine,add_zero]
    have hp:= Lining.Ferry.sheet_launch c (q+step i) s; rw [h,map_add,h0,wrap_step] at hp
    exact (show ap c (q+step i)=seam 0 x i from TorusPCAC.Geometry.seam_step x i) ▸ hp
lemma step_prism (P: Ratio c f)(x:Site c) : prism s (P.embed x)=prism s x:=by
    rw [prism,show sheet (P.embed x)= _ from TorusPCAC.Geometry.hop_child P x]; rw [show s.act (P.count.val • TorusPCAC.Stencil.nonnegative x)=P.count.val • s.act (sheet x) from map_nsmul s.actEquiv _ _]; exact degree_child ..
lemma rotor (M: Spike) : copies 6 (hues (0:Site c) s (prism s) M) = Action.moved s (star M):=by
    ext ⟨⟨x,i⟩,u⟩ ⟨⟨y,j⟩,v⟩; by_cases h:u=v <;> by_cases he:s.act x=y <;> simp [copies,hues,Matrix.blockDiagonal_apply, Lat.rides,Action.moved,h, he,Ne.symm,eq_comm,← wrap_signed,Lining.Ferry.sheet_unit,affine,shiftE,prism, show s.actEquiv x=s.act x from rfl] -- shiftE
lemma dir_sail (M:Spike) : UV.Mstar (Action.moved s M (n:=c) (F:=6))= Action.moved s (Mstar M):=by
    ext i j; conv_rhs=> unfold Action.moved; simp only [Matrix.of_apply,← mstar_wave]
    by_cases h:j.2=i.2∧j.1.1=wrap c (s.act (sheet i.1.1))
    · simp only [UV.mstar,Action.moved,Matrix.of_apply,if_pos h,star_mul,Lining.Ferry.ap_star,mul_comm]
    simp [UV.mstar,Action.moved,h]
lemma pinned (F:Massive.Density c 6) : Action.pin p s F= post s p.matrix.val 0 (prism s) F:=by
    funext i; unfold Action.pin post crank Kit.disguise; rw [rotor,← mstar_sq,dir_sail]; have h: star p.matrix.val=p.matrix⁻¹.val:=by
       calc _ = star p.matrix.val*(p.matrix.val*p.matrix⁻¹.val):=by rw [show p.matrix.val*p.matrix⁻¹.val=1 from p.matrix.val_inv,mul_one]
            _ = _ := by rw [← mul_assoc,p.isUnitary.1,one_mul]
    rw [mstar_sq (star p.matrix.val),star_star,h]
end YM.Massive.Patria
#print axioms YM.Massive.Patria.step_brute
#print axioms YM.Massive.Patria.smoke
