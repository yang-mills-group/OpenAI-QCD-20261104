import YM.QCD.Smoke.Curve

/-! # Schur determinant mismatch under noncoincident windings -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {f c F C : Side}{M:ℕ}{a b d u:ℝ}
lemma chip_stream {L:Window f F M}{A:Sheet F}{B:Sheet f}{d:Site F→ℂ}(h:A*stream L d=stream L d*B)(i:ℕ):logchip A i*stream L d=stream L d*logchip B i:=by
  have he i : A^i*stream L d= stream L d* B^i:=by induction i with
                                             | zero=> simp
                                             | succ i ih=> rw [pow_succ,pow_succ, Matrix.mul_assoc,h,← Matrix.mul_assoc,ih,Matrix.mul_assoc]
  rw [logchip,logchip,Matrix.neg_mul,Matrix.mul_neg,Matrix.smul_mul,Matrix.mul_smul,he]
lemma log_stream {L:Window f F M}{A:Sheet F}{B:Sheet f}{p:Site F→ℂ}(h:A*stream L p=stream L p*B)(ha:‖notch d A‖<1)(hb: ‖notch d B‖<1): lap (notch d A)*stream L p=stream L p*lap (notch d B):=by
  have hv : notch d A*stream L p=stream L p*notch d B:=by simp only [notch,Matrix.mul_sub, Matrix.sub_mul,Matrix.smul_mul, Matrix.mul_smul,h]; simp
  let U : Sheet f→L[ℂ] Rail F f:=LinearMap.toContinuousLinearMap { toFun:=fun i=> stream L p*i,map_add':=fun _ _=> Matrix.mul_add ..,map_smul':=fun _ _=>Matrix.mul_smul .. }
  let V: Sheet F→L[ℂ] Rail F f:=LinearMap.toContinuousLinearMap { toFun:=fun i=> i*stream L p,map_add':=fun _ _=> Matrix.add_mul ..,map_smul':=fun _ _=> Matrix.smul_mul .. }
  change V (∑' i, logchip (notch d A) i)=U (∑' i, logchip (notch d B) i); rw [V.map_tsum (log_series ha), U.map_tsum (log_series hb)]; exact tsum_congr fun i=>chip_stream hv i
lemma window_separated (L: Window f F M) (x y: Site F)(h:x≠y)(hh: L.cut x=L.cut y): f.val≤ separation x y:=by
  let z:= Lattice.lift (x-y); have ht:=L.port y z; rw [show y + wrap F z=x from (by unfold z; rw [wrap_lift]; abel),hh] at ht
  have hz : wrap f z=0:=by rw [← add_right_inj (L.cut y),add_zero]; exact ht.symm
  obtain ⟨j,hj⟩ : ∃ j,z j ≠0:=by by_contra! hp; have he:z=0:=funext hp; have hi:= wrap_lift (x-y); rw [show lift (x-y)=_ from he,map_zero] at hi; exact h (sub_eq_zero.mp hi.symm)
  have he : ((z j:ℤ):ZMod f.val)=0:=congr_fun hz j
  have hui : (f.val:ℤ)∣z j:= (ZMod.intCast_zmod_eq_zero_iff_dvd ..).1 he
  obtain ⟨p,H⟩:=hui; have hh : f.val ∣(z j).natAbs:=by rw [H,Int.natAbs_mul]; exact ⟨_,rfl⟩
  exact le_trans (Nat.le_of_dvd (by omega) hh) (component_le ..)

def lantern (C:ℝ)(a:ℝ):= C*countCost (a/2)*(Fintype.card Fiber:ℝ)
lemma lantern_pos (ht:0≤d)(ha:0<a):0≤lantern d a:=mul_nonneg (mul_nonneg ht (count_pos (by positivity)).le) (by positivity)
lemma lint (x: Site F)(S:Sheet f)(T:Sheet F)(i:Fiber)(r:Site F→ℂ)(L: Window f F M)(hQ:Quaint L r)(he:T*stream L r=stream L r*S)(hz:0 ≤ b)(ha:0<a)(hc:∀ y:Site F, ‖T (x,i) (y,i)‖ ≤ b*Decay a x y):
    ‖S (L.cut x,i) (L.cut x,i)-T (x,i) (x,i)‖ ≤ b*Real.exp (-(a/2)*f.val)*countCost (a/2):=by
  let Q (j:Site F):ℂ:= if L.cut j=L.cut x then r j*T (x,i) (j,i) else 0
  have he : ∑ j,Q j=r x*S (L.cut x,i) (L.cut x,i):=by
    have hP:= velvet L r T S he x (L.cut x)
    have hh := Matrix.ext_iff.mpr hP i i; rw [Matrix.sum_apply] at hh
    rw [← show _=r x*S _ _ from hh.symm]; apply sum_congr rfl; intro j _; unfold Q; split <;> rfl
  let A:= univ.erase x; have hU : Q x = r x * T (x,i) (x,i):=if_pos rfl
  have hi: ∑ j∈A,Q j=r x*(S (L.cut x,i) (L.cut x,i)-T (x,i) (x,i)):=by
    have hp:= Finset.add_sum_erase _ Q (mem_univ x); rw [he,hU] at hp; rw [mul_sub]; unfold A; grind
  have hm y : ‖r y‖=1:=by rcases hQ.sign y with h|h <;> simp [h]
  have hb:0<a/2:=by positivity
  let K:= b*Real.exp (-(a/2)*f.val); have hv:0≤K:=mul_nonneg hz (by positivity)
  have hh (z) (hz':z∈A):‖Q z‖≤K*Decay (a/2) x z:=by
    unfold Q; split; swap; · rw [norm_zero]; exact mul_nonneg hv (Push.Uniform.decay_pos ..).le
    next hp=> rw [norm_mul,hm,one_mul]; apply (hc z).trans; unfold K; rw [mul_assoc,Decay,Decay, ← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hz; apply Real.exp_monotone
              have ht : (f.val:ℝ)≤separation x z:=by exact_mod_cast window_separated L x z (ne_of_mem_erase hz').symm hp.symm
              nlinarith
  rw [← one_mul ‖_ - _‖, ← hm x,← norm_mul, ← hi]; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i h=> hh i h)).trans
  change ∑ i∈ A, K * _ ≤ K*_; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (t:=univ) (subset_univ A) (fun _ _ _=> (Push.Uniform.decay_pos ..).le)).trans (decay_count hb _)) hv
lemma draft (x:Site F) (S:Sheet f)(T:Sheet F)(r:Site F→ℂ)(L: Window f F M)(hQ:Quaint L r)(he:T*stream L r=stream L r*S)(hz:0 ≤ b)(ha:0<a)(hc:∀ (y:Site F) i, ‖T (x,i) (y,i)‖ ≤ b*Decay a x y):
    ‖(Run.cell S (L.cut x) (L.cut x)).trace.re-(Run.cell T x x).trace.re‖ ≤ lantern b a*Real.exp (-(a/2)*f.val):=by
  rw [← Complex.sub_re,Real.norm_eq_abs]; apply Complex.abs_re_le_norm _|>.trans
  simp only [Matrix.trace,← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans
  apply (sum_le_sum (s:=univ) (fun i _=> (lint x S T i r L hQ he hz ha (fun j=>hc j i)))).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul]; unfold lantern; ring
end YM.QCD.Smoke
