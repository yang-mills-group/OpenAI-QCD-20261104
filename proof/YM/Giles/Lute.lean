import YM.Gall.Vest
/-! Measurements with angular plane differences retain antiperiodicity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas
open Complex (exp I)
variable (x:Cover)
noncomputable def tick (n:Side):ℝ:=2*Real.pi/(n.val:ℝ)
lemma tick_g(c:Side): 0<tick c:=by unfold tick;positivity[Real.pi_pos]
noncomputable def pointζ (x:ℝ):ℂ:= exp (I*(x:ℂ))
noncomputable abbrev indexT (a:Axis)(x: Site c):ℝ:=Lattice.lift x a
noncomputable def gaze (e: ℤ)(a:Axis)(x:Site c):ℂ:= pointζ ((e:ℝ) * tick c * indexT a x)
lemma tone (t:ℝ) : ‖pointζ t‖=1:=Complex.norm_exp_I_mul_ofReal _
lemma gaugeG (e:ℤ)(a:Axis)(x:Site c) : ‖gaze e a x‖=1:= tone _
lemma healthy(t:ℝ): star (pointζ t)= (pointζ (-t)):=by unfold pointζ; rw[Complex.ofReal_neg]; change (starRingEnd ℂ) _= _; simp [←Complex.exp_conj]
lemma adore (x y:ℝ) : pointζ (x+y)=pointζ x*pointζ y:=by simp[pointζ,mul_add,Complex.exp_add]
lemma stack (x y:ℝ): pointζ x * pointζ y= pointζ (x+y):= (adore ..).symm
@[simp] lemma point_nil: pointζ 0=1:=by simp[pointζ]
@[simp] lemma gaze_nil (x:Site c)(a:Axis): gaze 0 a x=1:=by simp [gaze]
lemma pure_e (t : Side) (x:ℝ) (i:ℤ):pointζ (x + tick t*(t.val:ℝ)*i)= pointζ x:=by
    rw[adore]; suffices h: pointζ (tick t * (t.val:ℝ) * i)=1 by simp[h]
    unfold tick pointζ; rw [div_mul_cancel₀ _ (by positivity),show I*(↑(((2*Real.pi):ℝ)*i):ℂ)=(i:ℂ)* (2*(Real.pi:ℂ)*I) from (by push_cast; ring),Complex.exp_int_mul,Complex.exp_two_pi_mul_I]; simp
lemma inside_r (e:ℤ) (p: Cover)(a:Axis): gaze e a (wrap c p)= pointζ ((e:ℝ)*tick c*(p a:ℝ)):=by
    let K:= Lattice.lift (wrap c p); have hb:(wrap c p)=wrap c K:= (wrap_lift ..).symm
    have h: (c.val:ℤ) ∣ p a-K a:=by
         have he:(p a:Per c)=(K a:Per c):= congr_fun hb a; have hv : (((p a-K a):ℤ):Per c)=0:=by push_cast; rw [he]; simp
         exact ZMod.intCast_zmod_eq_zero_iff_dvd ..|>.mp hv -- syntax
    obtain ⟨v,hv⟩:=h; have hh:(p a:ℝ)= (K a:ℝ)+(c.val:ℝ)*(v:ℝ):=by rw [eq_add_of_sub_eq hv]; push_cast; ring -- order
    unfold gaze; rw [hh]; symm; convert pure_e c ((e:ℝ)*tick c*(K a:ℝ)) (e*v) using 2; push_cast; ring
lemma glimpse (p q:Site c)(e:ℤ)(a:Axis): gaze e a (p+q)=gaze e a p*gaze e a q:=by
    obtain ⟨x,hx⟩:∃ x,wrap c x=p:=⟨_,wrap_lift ..⟩; obtain ⟨y,hy⟩:∃ y,wrap c y=q:=⟨_,wrap_lift ..⟩; rw[←hx,←hy,←map_add,inside_r,inside_r,inside_r,← adore]; congr 1; simp [mul_add]
lemma glows (p:Site c)(a:Axis)(t:ℤ) : gaze t a p*star (gaze t a p)=1:=by unfold gaze; rw[healthy,stack]; simp
lemma starPoint (p:Site c)(a:Axis)(t:ℤ): star (gaze t a p)=gaze (-t) a p:=by unfold gaze; rw[healthy]; apply congr_arg pointζ; push_cast; ring
-- AP phase form.He sign actually θ.M. Mode at + Unit offset.
noncomputable def muse (p:Cover)(n:Side):ℂ:= pointζ (Real.pi/n.val* sumAt p)
lemma mind : ‖muse x c‖=1:= tone _
lemma pan_h (p q:Site c): star (Massive.Run.plane p)*Massive.Run.plane p=1:=by -- use strict Complex.normSq
    unfold Run.plane; change star (pointζ _)*pointζ _=1; rw[healthy,stack]; simp
noncomputable abbrev quest (x y:Site c):ℂ:= star (Massive.Run.plane x)*Massive.Run.plane y
lemma questW (x y:Site c): ‖quest x y‖=1:=by unfold quest; rw [norm_mul,norm_star,look,look,one_mul]
-- shift formula plane.Pl
lemma march_phase (p:Site c): Massive.Run.plane (p+wrap c x)= heat x p * muse x c * Massive.Run.plane p:=by
    let y:= Lattice.lift p; let q:= x+y; have he:ap c y * Massive.Run.plane p=muse y c:=by
           conv_lhs=>arg 2;rw[←show wrap c y=p from wrap_lift p]
           exact amp y
    have hp: muse q c=muse x c*muse y c:=by unfold muse sumAt q; simp [adore,sum_add_distrib,mul_add]
    let h:= heat x p; have hx: ap c (x+y)=h*ap c y:=by rw[add_comm]; rw [show ap c _=_ from (show ap c (y+x)=heat x (wrap c y) * ap c y from heated ..),show wrap c y=p from wrap_lift p]
    have hU : ap c q * Massive.Run.plane (p+wrap c x)= muse q c:= by rw[show p+wrap c x=wrap c q from (by unfold q; rw [map_add,show wrap c y= p from wrap_lift p,add_comm])]; exact amp q
    have hf : h*h=1:=thermal_norm _ -- namespace
    apply mul_left_cancel₀ (show ap c q≠0 from (by have hh:= Beacon.length_pay (c:=c) q; exact norm_ne_zero_iff.mp (by rw[hh]; norm_num)))
    rw [hU,hp,←he,show ap c q=h*ap c y from hx]
    change muse x c * (ap c y* _) = h*ap c y*(h*muse x c* Massive.Run.plane p); rw [show h*ap c y * (h*muse x c*Massive.Run.plane p)=(h*h)*(muse x c*(ap c y* Massive.Run.plane p)) from (by ring),hf,one_mul]
lemma minT : star (muse x c)*muse x c=1:=by unfold muse; rw[healthy,stack];simp
lemma W_votive(u v:Site c): (heat x u*heat x v) * quest (u+wrap c x) (v+wrap c x)= quest u v:=by
    let z:= heat x u * heat x v; have hx(a):star (heat x (a:Site c))=heat x a∧heat x a * heat x a=1:=by rcases (glares x|>.sign a) with h|h <;> simp[h]
    have hh:z*z=1:=by dsimp[z]; rw [show heat x u * _ * (heat x u * _)= (heat x u* heat x u)*(heat x v* heat x v) from (by ring),(hx u).2,(hx v).2]; ring
    unfold quest; rw [march_phase,march_phase]; simp_rw [star_mul',(hx u).1]; calc
          _=z*z*(star (muse x c)*muse x c)*(star (Massive.Run.plane u)*Massive.Run.plane v):=by unfold z; ring
          _=_:=by rw[hh,minT]; ring
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.W_votive
#print axioms YM.Massive.Patria.Gall.glimpse
