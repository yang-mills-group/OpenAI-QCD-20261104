import YM.Gall.Cream
/-! Linear decomposition of translated jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole
open Poised Poised.Display Poised.Beacon PCAC Push.Local Rudder
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
variable (g:su.Color)
local notation "Y★"=> Cray c
local notation "cv"=> kiln g
local notation "K"=> ink g
variable (X:Labels.Taylor su 0)(Y:Labels.Taylor su 1)
local notation "E₀"=> E4
local notation "C₀"=> su.Color
noncomputable def normT (X:Labels.Taylor su 0)(i:Axis):= continuousMultilinearCurryFin1 ℝ E₀ C₀ (X.val i)
lemma normT_val(i:Axis)(x:E₀): normT X i x=X.value i x:=by rw[normT,continuousMultilinearCurryFin1_apply]; apply congr_arg; ext a; fin_cases a; simp
noncomputable def peakT (Y:Labels.Taylor su 1)(i:Axis):= (continuousMultilinearCurryFin1 ℝ E₀ C₀).toContinuousLinearEquiv.toContinuousLinearMap.comp ((Y.val i).curryLeft)
lemma peakT_val(i:Axis)(x y:E₀): peakT Y i x y= Y.val i ![x,y]:=by rw[peakT]; change continuousMultilinearCurryFin1 ℝ E₀ C₀ ((Y.val i).curryLeft x) y= _; rw [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply]; congr 1; ext j; fin_cases j <;> simp -- test
lemma topT(i:Axis)(x:E₀): peakT Y i x x=Y.value i x:=by rw [peakT_val]; apply congr_arg; ext a; fin_cases a<;>rfl
lemma peakT_symm(i:Axis)(x y:E₀): peakT Y i x y= peakT Y i y x:=by
    rw[peakT_val,peakT_val]; apply Eq.trans _ (Y.property.1 i _ (Equiv.swap 0 1)); congr! 1; ext a; fin_cases a<;> simp
open StressFlux (curl0 curl1)
noncomputable def radial (Y:Labels.Taylor su 1)(z:Axis): Labels.Taylor su 0:= (1/2:ℝ) • ∑ i:Axis, ∑ j:Axis, StressFlux.leg0 i j (curl1 z i j Y)
variable (i j k:Axis)
lemma radialC: curl0 i j (radial Y k)=curl1 k i j Y:=by
    have hf(l r:Axis) := StressFlux.curl0_leg l r i j (curl1 k l r Y)
    rw[radial]; simp_rw[map_smul,map_sum,hf,basis_eq]; have h(i j:Axis):curl1 k i j Y= -curl1 k j i Y:= StressFlux.curled_swap Y _ _ _
    have hp := h i j; simp only[sub_smul,ite_mul,mul_ite,zero_mul,mul_zero,one_mul,ite_smul,one_smul,zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]; rw [hp]; simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]; module
noncomputable def sunD (Y: Labels.Taylor su 1)(i:Axis)(x:E4): E4→L[ℝ] su.Color:= (2:ℝ) • (peakT Y i x) -- scalar n=2? annotate
lemma peakD(i k:Axis)(x:E4): Maxwell.grad k (Y.value i) x=sunD Y i x (basis k):=by
    unfold Maxwell.grad YM.Analysis.D Labels.Taylor.value; rw [YM.Tensor.differential_diagonal]; change (1+1:ℕ) • _= (2:ℝ) • peakT Y i x (basis k); rw[peakT_symm]; apply Eq.trans _ ((Nat.cast_smul_eq_nsmul ℝ 2 _).symm); apply congr_arg; rw [ContinuousMultilinearMap.curryLeft_apply,peakT_val]; apply congr_arg; ext j; fin_cases j<;> rfl
    exact Y.property.1 i -- edit
lemma curl1B : curl1 k i j Y=sunD Y j (basis k) (basis i)-sunD Y i (basis k) (basis j):=by
    unfold curl1; rw [StressFlux.curled_deriv]; rw [peakD,peakD]
lemma dawnT(x v:E4) : Y.value i (x+v)= Y.value i x+sunD Y i v x+Y.value i v:=by
    rw [←topT,←topT,←topT]; simp only [map_add, ContinuousLinearMap.add_apply]; rw [peakT_symm Y i v x]; change _ = _+(2:ℝ) • peakT Y i v x+_; rw [peakT_symm Y i v x]; module
lemma shineT(x v:E4)(hY:Along g Y): inner ℝ g (sunD Y i v x) • g=sunD Y i v x:=by
    have hp: sunD Y i v x= Y.value i (x+v)-Y.value i x-Y.value i v:=by rw [dawnT]; abel
    rw[hp,inner_sub_right,inner_sub_right,sub_smul,sub_smul,hY i (x+v),hY i x,hY i v]
private lemma polar_sm(a:ℝ)(X:Labels.Taylor su 0)(h:Along g X): Along g (a • X):=by intro i x; change inner ℝ g (a • X.value i x) • g=a • X.value i x; simp only [real_inner_smul_right,mul_smul,h i x]
private lemma along_fin {I:Type*}(f:I→Labels.Taylor su 0)(s:Finset I)(h:∀ i, Along g (f i)):Along g (∑ i∈s, f i):=by
    induction s using Finset.induction_on with | empty=> rw[sum_empty]; exact along0 g _ | insert i s hv ih=>rw [sum_insert hv];exact along_add g _ _ (h i) ih
lemma radialG(hY:Along g Y)(hh:‖g‖=1) : Along g (radial Y i):=by
    refine polar_sm g _ _ (along_fin g _ _ (fun a=> along_fin g _ _ (fun b=>?_)))
    let v:=curl1 i a b Y; have hv: inner ℝ g v • g=v:=by
         unfold v; rw[curl1B,inner_sub_right,sub_smul]
         rw [shineT g Y _ _ _ hY,shineT g Y _ _ _ hY]
    change Along g (StressFlux.leg0 a b v); rw [← hv,map_smul]; exact polar_sm g _ _ (along_leg0 g _ _ hh)
-- Symmetric compensation linear plus constants
noncomputable def gone (z:su.Color)(Y:Labels.Taylor su 1)(u i:Axis): E4→L[ℝ]ℝ:= (innerSL ℝ z).comp (sunD Y i (basis u)-normT (radial Y u) i)
lemma goneT(x:E₀) : gone g Y k i x= inner ℝ g (sunD Y i (basis k) x)-axisC g (radial Y k) i x:=by unfold gone; rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,normT_val]; change inner ℝ g (_-_) = inner ℝ g _ - axisC _ _ _ _; unfold axisC; rw[inner_sub_right]
lemma goneR : gone g Y k i (basis j)= gone g Y k j (basis i):=by
    have hp:=congr_arg (inner ℝ g) (radialC Y i j k); rw [StressFlux.curl0_value,curl1B,inner_sub_right, inner_sub_right] at hp; rw [goneT,goneT]; unfold axisC; linarith
lemma minusWave(i:Axis)(x y:E₀) : axisC g X i (x+y)=axisC g X i x+axisC g X i y:=by unfold axisC; rw[← normT_val,← normT_val,← normT_val,map_add,inner_add_right]
lemma minusWind (k i:Axis)(x:E₀)(t:ℝ) : axisC g Y i (x+t • basis k)=axisC g Y i x+t*axisC g (radial Y k) i x+t*gone g Y k i x+(axisC g Y i (t • basis k)):=by
    unfold axisC; rw [dawnT]; rw [show sunD Y i (t • basis k) x=t • sunD Y i (basis k) x from (by unfold sunD; rw[map_smul]; change (2:ℝ) • (t • peakT Y i (basis k) x)= t • ((2:ℝ) • peakT Y i (basis k) x); module),inner_add_right,inner_add_right,real_inner_smul_right,goneT]; unfold axisC; ring
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.minusWind
#print axioms YM.Massive.Patria.Gall.radialG
