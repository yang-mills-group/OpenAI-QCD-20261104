import YM.Gall.Scoot
/-! Pulled Cartan probe gradients at integer shifts. Within taper difference compact at O(1/c) using high power metrics. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace Interval
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "Y★"=> Cray c
-- potentials represented by polynomials
noncomputable def adept(A:Axis→E4→L[ℝ]ℝ): E4→L[ℝ]E4→L[ℝ]ℝ:=∑ i:Axis, (innerSL ℝ (basis i)).smulRight (A i)
lemma adeptV (A:Axis→E4→L[ℝ]ℝ)(x y:E4): adept A x y=∑ i:Axis,x i * A i y:=by
    unfold adept; simp [_root_.sum_apply]
lemma adept_basis (A:Axis→E4→L[ℝ]ℝ)(i:Axis)(x:E4): adept A (basis i) x=A i x:=by rw[adeptV]; simp
lemma adeptS(A:Axis→E4→L[ℝ]ℝ)(he:∀ i j:Axis,A i (basis j)=A j (basis i))(x y:E4): adept A x y=adept A y x:=by
    rw [adeptV,adeptV]; have hp (x:E4): (∑ i:Axis,x i • basis i) = x:=by ext i; simp
    have hh(i:Axis)(x:E4): A i x= ∑ j:Axis,x j * (A i (basis j)):=by nth_rw 1 [← hp x]; simp
    conv_lhs=> arg 2; intro i; rw [hh, Finset.mul_sum]
    conv_rhs=> arg 2; intro i; rw [hh, Finset.mul_sum]
    rw [Finset.sum_comm]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rw[he,mul_left_comm]
noncomputable def alo (A:Axis→ℝ): E4→L[ℝ]ℝ:= ∑ i:Axis, A i • innerSL ℝ (basis i)
lemma aloB(A:Axis→ℝ)(k:Axis): alo A (basis k)=A k:=by unfold alo; simp [_root_.sum_apply,ite_mul,mul_ite]
noncomputable def curveT (V:E4→L[ℝ]E4→L[ℝ]ℝ)(U:E4→L[ℝ]ℝ)(x:E4):ℝ:=V x x/2 + U x
lemma curveCost (V:E4→L[ℝ]E4→L[ℝ]ℝ)(U:E4→L[ℝ]ℝ): Dart 2 (fun c=> glaze (fun i:Site c=> curveT V U (lit i))):=by
    refine frost _ (a:=‖V‖+‖U‖) (fun t=>?_) (by positivity)
    let r:=‖t‖; have hr:0≤r:=norm_nonneg _; unfold curveT; rw[add_mul (‖V‖)]; apply (norm_add_le ..).trans; apply add_le_add; swap
    · apply (U.le_opNorm _).trans; gcongr; nlinarith [norm_nonneg t]
    apply le_trans (b:=‖V t t‖) (by rw [norm_div, Real.norm_ofNat]; exact div_le_self (norm_nonneg _) (by norm_num)); refine ((V t).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (V.le_opNorm t) (norm_nonneg _)).trans ?_); rw [mul_assoc, ← sq]; gcongr; linarith
lemma slopeV (V:E4→L[ℝ]E4→L[ℝ]ℝ)(U:E4→L[ℝ]ℝ)(hV:∀ x y:E4,V x y=V y x)(x:E4)(i:Axis): (∫ s in (0:ℝ)..1, V (basis i) (x+s • basis i)+U (basis i))= curveT V U (x+basis i)-curveT V U x:=by
    let p:= basis i
    let f(s:ℝ):=V p x+s*V p p+U p; have he(s:ℝ): V p (x+s • p)+U p=f s:=by simp [f,map_add]
    have hh : (∫ s in (0:ℝ)..1,V p (x+s • p)+U p)= V p x+(V p p)/2 + U p:=by
          simp_rw [he]; unfold f; rw [intervalIntegral.integral_add,intervalIntegral.integral_add]; rw [intervalIntegral.integral_const,intervalIntegral.integral_const, intervalIntegral.integral_mul_const]; simp; ring
          all_goals apply Continuous.intervalIntegrable <;> fun_prop
    rw [show (∫ s in (0:ℝ)..1, V (basis i) (x+s • basis i)+U (basis i))= _ from hh]; unfold curveT; simp only[map_add, ContinuousLinearMap.add_apply]; rw [hV x (basis i)]; unfold p; ring
lemma step_vec (u:Cover) (a:Axis):vector (u+step a)=vector u+basis a:=by
    ext j; rw [PiLp.add_apply,basis_eq]; simp [vector,step_apply]
lemma stepNeg_vec (u:Cover) (a:Axis): vector (u+ -step a)=vector u-basis a:=by
    have h:=step_vec (u+ -step a) a; rw [neg_add_cancel_right] at h; rw[h,add_sub_cancel_right]
variable (T:Taper)(g:su.Color)
def frost0 (u:Site c):Prop:=8*(pdist u+3)<c.val
include T
lemma lift_c (u:Site c)(a:Axis)(hu:frost0 u) : lit (u+step a)= lit u + basis a :=by
      rw [← wrap_step]
      unfold lit; rw [(Oriole.charts u (step a) T ((flipT (c:=c) _ _ (.inl rfl)).2) (by unfold frost0 at hu;omega)).2.1,step_vec]
lemma lift_d (u:Site c)(a:Axis)(hu:frost0 u) : lit (u - step a) = lit u - basis a:= by
      rw [←wrap_step, sub_eq_add_neg, ←map_neg]; unfold lit; rw [(Oriole.charts u (-step a) T ((flipT (c:=c) _ _ (.inr rfl)).2) (by unfold frost0 at hu;omega)).2.1,stepNeg_vec]
lemma towing (V:E4→L[ℝ] E4→L[ℝ]ℝ)(U:E4→L[ℝ]ℝ)(h:∀ x y:E4,V x y=V y x)(e: Edge (Site c))(hu: frost0 e.1): glaze (fun i=> curveT V U (lit i)) e= ∫ t in (0:ℝ)..1,V (basis e.2) (wake e t)+U (basis e.2):=by
     change curveT V U (lit (e.1+step e.2)) - curveT V U (lit e.1)=_; rw [lift_c T _ _ hu]; exact (slopeV V U h _ e.2).symm
lemma ivoryT (e:Edge (Site c))(t:ℝ)(he:t∈Set.Icc 0 1)(hv:8*(pdist e.1+1)< c.val): sailT T e t=1:=by
     apply T.near; intro i; have ht := component_le e.1 i
     let x:=Lattice.lift e.1; have hX: |((x i:ℤ):ℝ)|≤ (pdist e.1:ℝ):=by rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]; exact_mod_cast ht
     change |(c.val:ℝ)⁻¹ * ((x i:ℝ)+t*basis e.2 i)|≤_; rw [abs_mul,abs_of_nonneg (by positivity), mul_comm, ←div_eq_mul_inv, div_le_iff₀ (by positivity)]
     apply (abs_add_le ..).trans; have h': |t*basis e.2 i| ≤1:=by
           rw [basis_eq]; split; · rw[mul_one,abs_of_nonneg he.1]; exact he.2
           · simp -- layout
     have hv : 8*((pdist e.1:ℝ)+1) < c.val:=by exact_mod_cast hv
     linarith
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.ivoryT
#print axioms YM.Massive.Patria.Gall.towing
