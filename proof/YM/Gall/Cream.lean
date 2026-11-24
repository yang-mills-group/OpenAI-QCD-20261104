import YM.Gall.Fill
import YM.Push.STRESS_FLUX.Polynomial
/-! Certified Abelian holonomic probes. Taper included. Coordinates linearized locally. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius TensorProduct Classical Interval
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole
open Poised Poised.Display Poised.Beacon PCAC Push.Local Rudder
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
variable (g:su.Color)
local notation "Y★"=> Cray c
local notation "cv"=> kiln g
local notation "K"=> ink g
noncomputable abbrev axisC (g:su.Color) (X:Labels.Taylor su j)(i:Axis)(x:E4): ℝ:= inner ℝ g (X.value i x)
abbrev Along (g:su.Color)(X:Labels.Taylor su j):=∀ i x,(axisC g X i x) • g=X.value i x
lemma candle (h X:ℝ)(hg:‖g‖=1)(F:su.Color)(hF:h • g=F): inner ℝ g F=h:=by rw [← hF]; norm_num [hg, real_inner_smul_right, real_inner_self_eq_norm_sq]
lemma along_leg0 (i j:Axis)(hg:‖g‖=1): Along g (StressFlux.leg0 i j g):=by intro k x; unfold axisC; rw[StressFlux.leg0_value,smul_sub,inner_sub_right]; split_ifs <;> norm_num [hg, real_inner_smul_right, real_inner_self_eq_norm_sq,mul_smul,← smul_neg] <;> module
lemma along_leg1 (i j k:Axis)(hg:‖g‖=1): Along g (StressFlux.leg1 i j k g):=by intro w x; unfold axisC; rw [StressFlux.leg1_value,smul_sub,inner_sub_right]; split_ifs <;> norm_num [hg, real_inner_smul_right, real_inner_self_eq_norm_sq,mul_smul,← smul_neg] <;> module
lemma along_sub (X Y:Labels.Taylor su j)(h:Along g X)(hp:Along g Y): Along g (X-Y):=by intro i x; change inner ℝ g (X.value i x-Y.value i x) • g=X.value i x-_; rw [inner_sub_right,sub_smul,h i x,hp i x]; rfl
lemma along_add (X Y:Labels.Taylor su j)(h:Along g X)(hp:Along g Y): Along g (X+Y):=by intro i x; change inner ℝ g (X.value i x+Y.value i x) • g=X.value i x+_; rw [inner_add_right,add_smul,h i x,hp i x]; rfl
lemma along0 (j:ℕ) : Along g (0:Labels.Taylor su j):=by intro i x; change inner ℝ g 0 • g=0; simp
noncomputable def leanY (X:Labels.Taylor su 0)(Y:Labels.Taylor su 1):Labels.Jet su:= Pi.single 0 X+Pi.single 1 Y
@[simp] lemma leanV0 (X Y) : leanY X Y 0=X:=by simp[leanY]
@[simp] lemma leanV1 (X Y) : leanY X Y 1=Y:=by simp[leanY]
def wake (i:Edge (Site c))(t:ℝ):E4:= vector (Lattice.lift i.1) +t • basis i.2
lemma wake_c (i: Edge (Site c)):Continuous (wake i):=by unfold wake; fun_prop
noncomputable def sailT(T:Taper)(i: Edge (Site c))(t:ℝ):ℝ:= T.χ ((c.val:ℝ)⁻¹ • wake i t)
lemma sail_c (T:Taper)(i: Edge (Site c)): Continuous (sailT T i):= T.smooth.continuous.comp ((wake_c i).const_smul (c.val:ℝ)⁻¹)
noncomputable def tinge (T:Taper)(X:Labels.Taylor su j) (i:Edge (Site c))(t:ℝ):ℝ:= sailT T i t* axisC g X i.2 (wake i t)
lemma tinge_c (T:Taper)(X:Labels.Taylor su j)(i: Edge (Site c)) : Continuous (tinge g T X i):=(sail_c T i).mul (continuous_const.inner ((YM.Tensor.diag_smooth (X.val i.2) ∞).continuous.comp (wake_c ..)))
noncomputable def fling (T:Taper)(X:Labels.Taylor su j): Cray c:=fun i=> ∫ t in 0..1,tinge g T X i t
noncomputable def glance (u:Labels.Taylor su 0)(v:Labels.Taylor su 1)(t:ℝ)(H:Taper): V₀:=cv (river (fling g H u) (fling g H v) t)
variable (T:TaperHol)(X:Labels.Taylor su 0)(Y:Labels.Taylor su 1)
lemma smirk (i:Edge (Site c))(t:ℝ)(h:ℝ)(hX:Along g X)(hY:Along g Y)(hd: 6 ≤ d):
   T.T.connection c d (leanY X Y) t (Lattice.lift i.1,i.2) h=(t^4*tinge g T.T X i h+t^6*tinge g T.T Y i h) • g:=by
    unfold Taper.connection Source.partConnection; let P:= leanY X Y
    change sailT T.T i h • (t^2 • potential _ _ _ (t^2 • wake i h))=_
    have hp(j:Axis)(x:E4):Source.potential (d/2) P j x=X.value j x+Y.value j x:=by
        unfold Source.potential; apply Eq.trans (Finset.sum_subset (s₂:=Finset.range (d/2-1)) (f:=fun i'=>(P i').value j x) (show Finset.range 2 ⊆ Finset.range (d/2-1) from Finset.range_mono (by omega)) ?_).symm; swap
        · intro l hl he; have hh:¬ l < 2:=fun h=> he (mem_range.mpr h); rw [show P l=0 from (by simp[P,leanY,(show l≠0 by omega),(show l≠1 by omega),Pi.single_eq_of_ne])]; rfl
        rw [Finset.sum_range_succ,Finset.sum_range_one]; rw[show P 0= X from leanV0 ..,show P 1=Y from leanV1 ..] -- check
    rw [hp]; unfold Labels.Taylor.value; rw [YM.Tensor.homogeneous, YM.Tensor.homogeneous]; unfold tinge; rw [add_smul,mul_smul,mul_smul,mul_smul,mul_smul,hX,hY]; unfold Labels.Taylor.value; module
lemma fizz (t:ℝ): HasDerivAt (fun x=> su.mat (bird g x)) (su.mat (bird g t)*su.colorMat g) t:=by unfold bird; simp only [su.mat_lieExp,map_smul]; exact hasDerivAt_exp_smul_const ..
lemma kicks (t:ℝ)(hX:Along g X)(hY:Along g Y)(hd:6 ≤ d): T.links c d (leanY X Y) t=glance g X Y t T.T:=by
    funext i; let F:=tinge g T.T X i; let G:=tinge g T.T Y i
    let w(h:ℝ):= t^4*(∫ x in 0..h,F x)+t^6*(∫ x in 0..h,G x); have hf(h:ℝ):HasDerivAt w (t^4*F h+t^6*G h) h:=by
           have he(H:ℝ→ℝ)(hv:Continuous H):HasDerivAt (fun u=>∫ x in 0..u, H x) (H h) h:= intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 h) hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
           exact ((he F (tinge_c ..)).const_mul (t^4)).add ((he G (tinge_c ..)).const_mul (t^6))
    let l:Edge Cover:=(Lattice.lift i.1,i.2); have hs:SolvesLink (bird g ∘ w) (T.T.connection c d (leanY X Y) t l):=by
       refine ⟨?_,fun h=>?_⟩; · simp [bird,w] -- bor
       let f:=su.mat ∘ bird g
       have hh := (fizz g (w h)).scomp h (hf h)
       apply hh.congr_deriv; rw [show (T.T.connection c d (leanY X Y) t l) h=_ from smirk ..,map_smul,mul_smul_comm]; all_goals first|assumption|rfl
    rw [show T.links c d _ t i=T.flow c _ (leanY X Y) t l 1 from rfl,(T.solves ..).unique hs]; rfl
lemma grow_flings (u v:Labels.Taylor su j): fling (c:=c) g T.T (u+v)= fling g T.T u+fling g T.T v:=by
    funext i; unfold fling; rw[Pi.add_apply]
    rw[show tinge g T.T (u+v) i= tinge g T.T u i + tinge g T.T v i from funext fun t=>by change _* inner ℝ g (u.value _ _+v.value _ _)= _; rw [inner_add_right,mul_add]; rfl]; exact intervalIntegral.integral_add ((tinge_c ..).intervalIntegrable ..) ((tinge_c ..).intervalIntegrable ..)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.kicks
