import YM.Kwick.Aria
/-! first coefficient exactly nonzero. -/
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
variable (e:ℤ)(a b:Axis)
lemma tick_rot : plenty c e a a=pointζ (tick c * (1/2+(e:ℝ))):=by
     unfold plenty; let X:= Lattice.step (S:=ℤ) a; rw[← wrap_step, inside_r e X a]; unfold muse; rw [stack]; refine congr_arg pointζ ?_; unfold X tick sumAt; simp [step_apply]; ring
lemma clock_rot(C:ℕ→Side)(t:ℝ)(hx:Tendsto (fun i=> ((C i).val:ℝ)) atTop atTop): Tendsto (fun i=> (Gall.helm (C i))⁻¹ * (pointζ (tick (C i)*t)-1)) atTop (𝓝 (t:ℂ)):=by
     apply tendsto_iff_norm_sub_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) (Eventually.of_forall fun i=> degree_t t (c:=C i)); simpa only [tick,mul_zero,zero_mul] using (((Filter.Tendsto.const_div_atTop hx (2*Real.pi)).const_mul 2).mul_const (‖t‖^2)) -- signature
lemma spike_clock(C:ℕ→Side)(hx:Tendsto (fun i=> ((C i).val:ℝ)) atTop atTop): Tendsto (fun i=>(Gall.helm (C i))⁻¹ *slope (C i) e a a) atTop (𝓝 (1/2+(e:ℂ))):=by
     let x:ℝ:= 1/2+(e:ℝ); let u(i:ℕ)(x:ℝ):= (Gall.helm (C i))⁻¹*(pointζ (tick (C i)*x)-1); have h:(2:ℂ)⁻¹*((x:ℂ)- ((-x:ℝ):ℂ))=(1/2+(e:ℂ)):=by unfold x; push_cast; ring
     rw[←h]; refine (((clock_rot C x hx).sub (clock_rot C (-x) hx)).const_mul (2:ℂ)⁻¹).congr (fun i=>?_); unfold slope; rw [tick_rot, Gall.healthy]; rw [show -(tick (C i) * _)= tick (C i)*(-x) from (mul_neg ..).symm]; unfold x; ring
lemma polar_clock (C:ℕ→Side)(hx:Tendsto (fun i=> ((C i).val:ℝ)) atTop atTop): Tendsto (fun i=> (Gall.helm (C i))⁻¹ * (slope (C i) 1 a a-slope (C i) 0 a a)) atTop (𝓝 1):=by
     simp_rw[mul_sub]; convert! (spike_clock 1 a C hx).sub (spike_clock 0 a C hx) using 1; congr 1; norm_num
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.polar_clock
