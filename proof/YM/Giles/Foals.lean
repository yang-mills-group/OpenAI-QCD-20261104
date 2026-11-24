import YM.Giles.Slat
/-! Polar Cartan compensation test: taking primitive x_ax_b/2 at lift. Sign choices certified. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace Interval
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
variable (T:Taper)(g:su.Color)(a b:Axis) (e:Edge (Site c))
noncomputable def rimV(a b:Axis)(x:Site c):ℝ:= (indexT a x*indexT b x)/2
noncomputable abbrev legV:= StressFlux.leg0 a b g
noncomputable def swapV (c:Side): Cray c:= arcT a b-fling g T (legV g a b)-glaze (rimV a b)
noncomputable def woodG(c:Side):Cray c:=monoT b - glaze (indexT b)
-- norms independent c for gradient fields
lemma norm_slot (x: E4): |x a| ≤ ‖x‖:=by rw [← basis_inner]; exact (abs_real_inner_le_norm ..).trans_eq (by rw [basis_norm,one_mul])
lemma windowF : Dart 2 (fun c=> glaze (c:=c) (rimV a b)):=by
    let f(x:E4):ℝ:= (x a * x b)/2; refine frost f (a:=1) (fun t=> ?_) zero_le_one; unfold f; rw [norm_div,norm_mul,Real.norm_ofNat]; apply le_trans (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)); apply (mul_le_mul (norm_slot ..) (norm_slot ..) (abs_nonneg _) (norm_nonneg t)).trans; rw [one_mul,←sq]; gcongr; linarith
lemma shelterF : Dart 1 (fun c=> glaze (c:=c) (indexT b)):=by
    let f(x:E4):ℝ:= x b; exact frost f (a:=1) (fun t=> (norm_slot b t).trans (by rw [pow_one,one_mul]; linarith)) zero_le_one
include T in
lemma untail (hh: frost0 e.1) (x:Axis): indexT x (e.1+step e.2) = indexT x e.1 + basis e.2 x:= congr_fun (congr_arg WithLp.ofLp (lift_c T e.1 _ hh)) x
lemma goldJ (hh:frost0 e.1)(hp:a≠b)(hx:‖g‖=1): swapV T g a b c e=0:=by
     let S(t:ℝ):= wake e t; have he(i:Axis)(t:ℝ): S t i=indexT i e.1 + t*(basis e.2 i):=rfl
     have hV(t:ℝ) (h:t∈Set.Icc 0 1): tinge g T (legV g a b) e t=((if e.2=b then S t a else 0)-(if e.2=a then S t b else 0))/2:=by
         unfold tinge legV axisC; rw [ivoryT _ _ _ h (by unfold frost0 at hh; omega),one_mul, StressFlux.leg0_value,real_inner_smul_right] -- edit
         rw [inner_sub_right]; split_ifs <;> simp [inner_smul_right,real_inner_smul_right, hx,real_inner_self_eq_norm_sq] <;> try ring
     have hz : fling g T (legV g a b) e= ((if e.2=b then indexT a e.1 else 0)-(if e.2=a then indexT b e.1 else 0))/2:=by
         let x:ℝ:= ((if e.2=b then indexT a e.1 else 0)-(if e.2=a then indexT b e.1 else 0))/2; unfold fling; change _=x
         calc _=(∫ t:ℝ in 0..1,x):= intervalIntegral.integral_congr (fun t ht=>by
                            rw [hV _ (by simpa using ht),he,he]; unfold x; by_cases ha:e.2=a; · rw[ha]; simp [hp,Ne.symm hp]
                            by_cases hb:e.2=b; · rw [hb]; simp [hp,Ne.symm hp]
                            simp [ha,hb])
              _=x:=by simp
     rw[swapV,Pi.sub_apply,Pi.sub_apply,hz,arcT,glaze]; unfold rimV; rw [untail T _ hh,untail T _ hh]; by_cases ha:e.2=a; swap
     · by_cases hb:e.2=b; · rw [hb]; simp [hp,hp.symm]; ring
       simp [ha,hb,basis_eq, Ne.symm ha, Ne.symm hb]
     simp [ha,hp,hp.symm]; ring
lemma dawnF (hp: a≠b)(hx:‖g‖=1): Dart 3 (skip0 (swapV T g a b)):=by
     have hm:Dart 2 (swapV T g a b):= dart_sub (dart_sub (dart_weaker (dart1 a b) (show 1≤ 2 from by norm_num)) (dart_weaker (listen T g (legV g a b)) (show 0+1 ≤ 2 from by norm_num))) (windowF _ _); exact darts hm fun c e h=> goldJ T g a b e h hp hx
include T in
lemma nightF : Dart 2 (skip0 (woodG b)):=by
     refine darts (show Dart 1 (woodG b) from dart_sub (dart_weaker (dart0 b) (show 0 ≤ 1 from by norm_num)) (shelterF _)) ?_; intro c e h; rw [woodG,Pi.sub_apply,monoT,glaze]; rw[untail T _ h]; split_ifs with h; rw[h]; simp; simp [h, Ne.symm h]
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.dawnF
#print axioms YM.Massive.Patria.Gall.nightF
