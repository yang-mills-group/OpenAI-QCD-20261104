import YM.Kai.Street
import YM.Kwick.Victor
/-! Support for U2 leading AP arithmetic. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {L c:Side}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls
variable (e:ℤ)(a b:Axis)(p u v:Site c)(X:Sheet c)(F: Grid c→ Sheet c)
local notation "Qm" x:arg=> Massive.Run.plane x
local notation "w"=> step (S:=ℤ) a
local notation "D"=> step (S:=Per c) a
noncomputable def pars (c:Side)(e:ℤ)(a:Axis)(x:Site c):ℂ:= Massive.Run.plane x * gaze e a x
noncomputable def plenty (c:Side)(e:ℤ)(a b:Axis):ℂ:= muse (step b) c*gaze e a (step b:Site c)
local notation "T"=> shift 0 (1:Grid c) a
lemma cost_step (x: Site c) : heat w x=seam 0 x a:= TorusPCAC.Geometry.seam_step x a
lemma px_turn (e:ℤ)(x:Site c): let p:= pars c e b; p (x+D)=seam 0 x a*plenty c e b a*p x:=by
     intro p; unfold p pars; rw[glimpse x D,show Qm (x+D)= seam 0 x a*muse w c*Qm x from ?_]; swap
     · have hp:= march_phase w x; rw [wrap_step,cost_step] at hp; exact hp
     unfold plenty; ring
lemma seamα(x:Site c): star (seam 0 x a)=seam 0 x a:=seam_real ..
lemma riches : star (plenty c e a b)*plenty c e a b=1:=by
     simp only [plenty,star_mul']; rw [show star (muse _ _)* _ * _= _ from (show star (muse (step b) c)*star (gaze e a (step b:Site c)) * (muse (step b) c*gaze e a (step b:Site c))=(star (muse (step b) c)*muse (step b) c)*(gaze e a (step b:Site c)*star (gaze e a (step b:Site c))) from by ring)]; rw[minT,glows,one_mul]
local notation "R!" i:arg j:arg=> if j=i+D then seam 0 i a else 0
lemma ridePlane(x y:Site c)(i j:Fiber): shift 0 (1:Grid c) a (x,i) (y,j)= (R! x y)*(1:Bundle) i j:=by
    unfold Lat.shift; rw [rr]; simp only[hop]; split; next h=>
           rw [if_pos h.symm]; unfold thread; simp only[Pi.one_apply]; rw [show colour (1:su.El)=1 from su.mat_one]; unfold touch; rw[Matrix.kronecker_smul,Matrix.one_kronecker_one]; rfl
    next h=> rw [if_neg (Ne.symm h),zero_mul]
-- functional tr spectral
noncomputable def arityG (c:Side)(P Q:Site c→ℂ)(i j:Fiber): Sheet c→ₗ[ℂ]ℂ := {
    toFun:= fun S=> ∑ u:Site c,∑ v:Site c, (star (P u)* Q v)* S (u,i) (v,j),map_add':= fun x y=>by simp only[Matrix.add_apply,mul_add,sum_add_distrib]
    map_smul':=fun x y=>by simp only[Matrix.smul_apply,Finset.mul_sum,smul_eq_mul,RingHom.id_apply]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=> mul_left_comm .. }
-- insertion multiplies shift. Define theorem eigen fixed vectors.L/R via mulVu/dot. star enough. general S arbitrary.
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.ridePlane
